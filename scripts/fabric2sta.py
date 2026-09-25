#!/usr/bin/env python3
"""fabric2sta.py fabric_t.v OUTDIR [--placement p.json] [--clock SITE_OR_NAME=PERIOD]...

OpenSTA's inputs from a timed extraction (tileverilog --timing):

  OUTDIR/netlist.v   the design as timing primitives -- one LUT per used
                     LUT output, connected only to the inputs its INIT
                     depends on; one FF per used register; a carry cell per
                     used carry; block RAMs, F7 muxes and inverters as they
                     are; every routed net a single wire
  OUTDIR/fast.lib    the primitives' arcs at the fast corner (min)
  OUTDIR/slow.lib    ...and at the slow corner (max)
  OUTDIR/delays.sdf  one INTERCONNECT per driver -> load from the pip sums
                     on the route, calibrated against Vivado
  OUTDIR/design.sdc  a clock on every clock root, async groups
  OUTDIR/run.tcl     the sta script that reads the lot

The library figures are Vivado's own, read off its paths (docs/extracted-
timing.md); the interconnect calibration likewise.  Run:

  sta -no_init -exit OUTDIR/run.tcl
"""
import json, os, re, sys
from collections import defaultdict

args = sys.argv[1:]
placement = None
clocks = {}          # site or cell-name substring -> period
while '--placement' in args:
    i = args.index('--placement'); placement = json.load(open(args[i + 1])); del args[i:i + 2]
while '--clock' in args:
    i = args.index('--clock'); k, v = args[i + 1].split('='); clocks[k] = float(v); del args[i:i + 2]
fabric, outdir = args[:2]
os.makedirs(outdir, exist_ok=True)

# ---- calibration and library figures (docs/extracted-timing.md) ----
CAL_MIN = (1.506, 0.076)
CAL_MAX = (1.246, 0.154)
LUT = (0.045, 0.124)
CLKQ = (0.100, 0.303)
FF_SETUP, FF_HOLD = 0.034, 0.087
CE_SETUP, CE_HOLD = 0.088, -0.011
BRAM_CLKQ = (1.200, 2.454)          # SDF: CLKARDCLK -> DOADO, RAM_MODE TDP, no output register
BRAM_SETUP = {'DI': 0.150, 'ADDR': 0.300, 'WE': 0.300, 'EN': 0.300, 'RST': 0.300, 'DIP': 0.150, 'REGCE': 0.300}
BRAM_HOLD = {'DI': 0.296, 'ADDR': 0.183, 'WE': 0.046, 'EN': 0.096, 'RST': 0.096, 'DIP': 0.296, 'REGCE': 0.096}
CY = (0.020, 0.060)                 # CARRY4 CI -> CO per bit; S -> CO
MUXF = (0.030, 0.090)
INV = (0.020, 0.050)

# ---- parse the fabric ----
text = open(fabric).read()
src_of, annot = {}, {}
fanout = defaultdict(list)
for m in re.finditer(r'^  assign (?:#\(([\d.]+):[\d.]+:([\d.]+)\) )?(\S+) = (\S+);', text, re.M):
    dst, s = m.group(3), m.group(4)
    if s in ("1'b0", "1'b1"): continue
    src_of[dst] = s; fanout[s].append(dst)
    annot[dst] = (float(m.group(1) or 0.02), float(m.group(2) or 0.02))
tied = {}
for m in re.finditer(r"^  wire (\S+) = 1'b([01]);", text, re.M):
    tied[m.group(1)] = m.group(2)
ports = set(re.findall(r'^  input wire (\S+)', text, re.M))
cols = []
for m in re.finditer(r'xcol #\((.*?)\)\s*\\(\S+) \((.*?)\);', text, re.S):
    params = {k: v.strip('"') for k, v in re.findall(r'\.(\w+)\(([^()]*)\)', m.group(1))}
    pins = dict(re.findall(r'\.(\w+)\(([^()]*)\)', m.group(3)))
    cols.append((m.group(2), params, pins))
insts = []   # (type, name, {pin: [wires msb..lsb] or wire})
for m in re.finditer(r'^  (RAMB36E1|RAMB18E1|INV|MUXF7|MUXF8|DSP48E1|MMCME2_ADV) \\(\S+) \((.*?)\);', text, re.M | re.S):
    pins = {}
    for pin, conn in re.findall(r'\.(\w+)\(([^()]*(?:\{[^{}]*\})?[^()]*)\)', m.group(3)):
        conn = conn.strip()
        if conn.startswith('{'):
            pins[pin] = [w.strip() for w in conn[1:-1].split(',')]
        elif conn:
            pins[pin] = conn
    insts.append((m.group(1), m.group(2), pins))
print(f'{len(src_of)} pips, {len(cols)} columns, {len(insts)} other instances', file=sys.stderr)

# ---- nets: every wire joined by a pip is one net; the root is the driver's wire ----
parent = {}
def find(w):
    while parent.get(w, w) != w:
        parent[w] = parent.get(parent[w], parent[w]); w = parent[w]
    return w
def union(a, b):
    ra, rb = find(a), find(b)
    if ra != rb: parent[ra] = rb
for d, s in src_of.items(): union(d, s)
def root_wire(w):
    seen = set()
    while w in src_of and w not in seen:
        seen.add(w); w = src_of[w]
    return w
delay_cache = {}
def wire_delay(w):
    """(fast_min, slow_max) of the route from the net's root to w, calibrated."""
    if w in delay_cache: return delay_cache[w]
    if w not in src_of:
        delay_cache[w] = (0.0, 0.0); return delay_cache[w]
    up = wire_delay(src_of[w]); a = annot[w]
    delay_cache[w] = (up[0] + a[0], up[1] + a[1]); return delay_cache[w]
sys.setrecursionlimit(200000)

def san(s):
    return re.sub(r'[^A-Za-z0-9_]', '_', s)
netname = {}
def net_of(w):
    """The wire's net name in the STA netlist."""
    if not w or w.startswith("1'b"): return None
    r = find(w)
    if r not in netname: netname[r] = san(root_wire(w) if root_wire(w) == r or True else r)
    return netname[r]
# name nets by the tree root (the driver's wire) rather than the union root
for w in list(src_of) + list(src_of.values()):
    r = find(w)
    if r not in netname: netname[r] = san(root_wire(w))

# ---- cells ----
cells = []                     # (libcell, name, {pin: net or [nets msb..lsb]})
drivers = {}                   # net -> "inst/pin" or "port"
loads = defaultdict(list)      # net -> [(inst, pin, wire)]
consts = {}
def tie(v):
    return f'TIE{v}'
def add_cell(kind, name, pins):
    cells.append((kind, name, pins))
def out(inst, pin, net, wire=None):
    if net: drivers[net] = f'{inst}/{pin}'
def load(inst, pin, net, wire):
    if net: loads[net].append((inst, pin, wire))

def lut_deps(init, five):
    """Which of A1..A6 (indices 0..5) the O6 (or O5) read of INIT depends on."""
    deps = []
    n = 5 if five else 6
    for i in range(n):
        for idx in range(1 << n):
            if (init >> idx) & 1 != (init >> (idx ^ (1 << i))) & 1:
                deps.append(i); break
    return deps

internal = {}
for inst, p, pins in cols:
    init = int(p['INIT'].split("'h")[1], 16)
    def pinnet(k):
        w = pins.get(k, '')
        return (net_of(w), w) if w and not w.startswith("1'b") else (None, None)
    ffsrc, ff5src, outmux, cy0 = p['FF_SRC'], p['FF5_SRC'], p['OUTMUX'], p['CY0']
    o6w, qw, muxw, cow = pins.get('O6', ''), pins.get('Q', ''), pins.get('MUX', ''), pins.get('CO', '')
    ci_w, fx_w, x_w = pins.get('CI', ''), pins.get('FX', ''), pins.get('X', '')
    # the nets each internal signal drives
    o6_net = net_of(o6w) if o6w else None
    o6_used = bool(o6_net) or ffsrc in ('O6',) or outmux == 'O6' or bool(cow) or ffsrc in ('XOR', 'CY') or outmux in ('XOR', 'CY')
    o5_used = ffsrc == 'O5' or ff5src == 'O5' or outmux == 'O5' or (cy0 == 'O5' and (bool(cow) or ffsrc in ('XOR', 'CY') or outmux in ('XOR', 'CY')))
    if o6_used and not o6_net: o6_net = f'{inst}_o6'
    o5_net = f'{inst}_o5' if o5_used else None
    mux_net = net_of(muxw) if muxw else None
    xo_net = f'{inst}_xo' if ffsrc == 'XOR' or outmux == 'XOR' else None
    co_net = net_of(cow) if cow else (f'{inst}_co' if ffsrc == 'CY' or outmux == 'CY' else None)
    q5_net = None
    # the output mux is wiring: whatever it selects IS the MUX wire's net
    sel = {'O6': o6_net, 'O5': o5_net, 'XOR': xo_net, 'CY': co_net}.get(outmux)
    if outmux == 'F7' or outmux == 'F8':
        sel = net_of(fx_w)
    if outmux == '5Q':
        q5_net = mux_net or f'{inst}_q5'
    elif mux_net and sel:
        # alias: rename the internal net to the MUX wire's net
        if sel.startswith(inst + '_'):
            if sel == o6_net: o6_net = mux_net
            if sel == o5_net: o5_net = mux_net
            if sel == xo_net: xo_net = mux_net
            if sel == co_net: co_net = mux_net
        else:
            # two physical wires carrying one signal (O6 pin and the MUX pin): merge
            union(muxw, o6w if sel == o6_net else fx_w)
            netname[find(muxw)] = sel
    # LUT cells
    if o6_net:
        deps = lut_deps(init, False)
        pn = {}
        for j, i in enumerate(deps):
            n, w = pinnet(f'A{i + 1}')
            if n: pn[f'I{j}'] = n; load(f'{inst}_L6', f'I{j}', n, w)
            else: pn[f'I{j}'] = tie(0)
        pn['O'] = o6_net; out(f'{inst}_L6', 'O', o6_net)
        add_cell(f'XLUT{max(1, len(deps))}', f'{inst}_L6', pn)
    if o5_net:
        deps = lut_deps(init & ((1 << 32) - 1), True)
        pn = {}
        for j, i in enumerate(deps):
            n, w = pinnet(f'A{i + 1}')
            if n: pn[f'I{j}'] = n; load(f'{inst}_L5', f'I{j}', n, w)
            else: pn[f'I{j}'] = tie(0)
        pn['O'] = o5_net; out(f'{inst}_L5', 'O', o5_net)
        add_cell(f'XLUT{max(1, len(deps))}', f'{inst}_L5', pn)
    # carry
    if co_net or xo_net:
        pn = {}
        pn['S'] = o6_net or tie(0)
        if cy0 == 'O5': pn['DI'] = o5_net or tie(0)
        else:
            n, w = pinnet('X'); pn['DI'] = n or tie(0)
            if n: load(f'{inst}_CY', 'DI', n, w)
        n, w = pinnet('CI'); pn['CI'] = n or tie(0)
        if n: load(f'{inst}_CY', 'CI', n, w)
        if co_net: pn['CO'] = co_net; out(f'{inst}_CY', 'CO', co_net)
        if xo_net: pn['XO'] = xo_net; out(f'{inst}_CY', 'XO', xo_net)
        add_cell('XCY', f'{inst}_CY', pn)
    # registers
    def ff(name, src, qnet):
        pn = {}
        if src == 'O6': pn['D'] = o6_net
        elif src == 'O5': pn['D'] = o5_net
        elif src == 'X':
            n, w = pinnet('X'); pn['D'] = n or tie(0)
            if n: load(name, 'D', n, w)
        elif src == 'XOR': pn['D'] = xo_net
        elif src == 'CY': pn['D'] = co_net
        elif src == 'F7F8':
            n, w = pinnet('FX'); pn['D'] = n or tie(0)
            if n: load(name, 'D', n, w)
        else: pn['D'] = tie(0)
        for k, lp in (('CLK', 'C'), ('CE', 'CE'), ('SR', 'R')):
            n, w = pinnet(k)
            pn[lp] = n or tie(1 if k == 'CE' else 0)
            if n: load(name, lp, n, w)
        pn['Q'] = qnet; out(name, 'Q', qnet)
        add_cell('XFF' if p['SYNC'].endswith('1') else 'XFFA', name, pn)
    if ffsrc != 'none':
        qn = net_of(qw) if qw else f'{inst}_q'
        ff(f'{inst}_FF', ffsrc, qn)
    if ff5src != 'none' and q5_net:
        ff(f'{inst}_FF5', ff5src, q5_net)

BUS = {'RAMB36E1': {'ADDRARDADDR': 16, 'ADDRBWRADDR': 16, 'DIADI': 32, 'DIBDI': 32, 'DIPADIP': 4, 'DIPBDIP': 4,
                    'DOADO': 32, 'DOBDO': 32, 'DOPADOP': 4, 'DOPBDOP': 4, 'WEA': 4, 'WEBWE': 8, 'ECCPARITY': 8, 'RDADDRECC': 9},
       'RAMB18E1': {'ADDRARDADDR': 14, 'ADDRBWRADDR': 14, 'DIADI': 16, 'DIBDI': 16, 'DIPADIP': 2, 'DIPBDIP': 2,
                    'DOADO': 16, 'DOBDO': 16, 'DOPADOP': 2, 'DOPBDOP': 2, 'WEA': 2, 'WEBWE': 4}}
RAM_SCALAR_IN = ['CLKARDCLK', 'CLKBWRCLK', 'ENARDEN', 'ENBWREN', 'REGCEAREGCE', 'REGCEB', 'REGCLKARDRCLK', 'REGCLKB',
                 'RSTRAMARSTRAM', 'RSTRAMB', 'RSTREGARSTREG', 'RSTREGB', 'CASCADEINA', 'CASCADEINB', 'INJECTDBITERR', 'INJECTSBITERR']
RAM_SCALAR_OUT = ['CASCADEOUTA', 'CASCADEOUTB', 'DBITERR', 'SBITERR']
for kind, name, pins in insts:
    iname = san(name)
    pn = {}
    if kind in ('RAMB36E1', 'RAMB18E1'):
        for pin, conn in pins.items():
            if isinstance(conn, list):
                nets = []
                for k, w in enumerate(conn):          # msb first
                    bit = len(conn) - 1 - k
                    n = net_of(w) if not w.startswith("1'b") else None
                    nets.append(n or tie(0))
                    if n:
                        if pin.startswith('DO') or pin in RAM_SCALAR_OUT or pin in ('ECCPARITY', 'RDADDRECC'): out(iname, f'{pin}[{bit}]', n)
                        else: load(iname, f'{pin}[{bit}]', n, w)
                pn[pin] = nets
            else:
                n = net_of(conn) if not conn.startswith("1'b") else None
                pn[pin] = n or tie(0)
                if n:
                    if pin in RAM_SCALAR_OUT: out(iname, pin, n)
                    else: load(iname, pin, n, conn)
        add_cell(kind, iname, pn)
    elif kind == 'INV':
        n, w = (net_of(pins['I']), pins['I']) if not pins['I'].startswith("1'b") else (None, None)
        pn['I'] = n or tie(0); load(iname, 'I', n, w)
        pn['O'] = net_of(pins['O']); out(iname, 'O', pn['O'])
        add_cell('XINV', iname, pn)
    elif kind in ('MUXF7', 'MUXF8'):
        for k in ('I0', 'I1', 'S'):
            w = pins.get(k, "1'b0"); n = net_of(w) if not w.startswith("1'b") else None
            pn[k] = n or tie(0)
            if n: load(iname, k, n, w)
        pn['O'] = net_of(pins['O']); out(iname, 'O', pn['O'])
        add_cell('XMUXF', iname, pn)
    elif kind == 'MMCME2_ADV':
        n = net_of(pins.get('LOCKED', ''))
        if n: pn['LOCKED'] = n; out(iname, 'LOCKED', n)
        add_cell('XMMCM', iname, pn)
    # DSP48E1: left out for now; its nets stay unconstrained

# ---- ports: nets no cell drives ----
allnets = set(drivers) | set(loads)
inputs = sorted(n for n in allnets if n not in drivers)
for n in inputs: drivers[n] = n
print(f'{len(cells)} cells, {len(allnets)} nets, {len(inputs)} undriven nets become inputs', file=sys.stderr)

# ---- netlist.v ----
with open(os.path.join(outdir, 'netlist.v'), 'w') as f:
    f.write('module fabric_sta (\n' + ',\n'.join(f'  input {n}' for n in inputs) + '\n);\n')
    f.write('  wire TIE0 = 1\'b0;\n  wire TIE1 = 1\'b1;\n')
    declared = set(inputs) | {'TIE0', 'TIE1'}
    for n in sorted(allnets):
        if n not in declared: f.write(f'  wire {n};\n'); declared.add(n)
    for kind, name, pn in cells:
        for v in pn.values():
            for n in (v if isinstance(v, list) else [v]):
                if n not in declared: f.write(f'  wire {n};\n'); declared.add(n)
        conns = ', '.join(f'.{k}({{{", ".join(v)}}})' if isinstance(v, list) else f'.{k}({v})' for k, v in pn.items())
        f.write(f'  {kind} {name} ({conns});\n')
    f.write('endmodule\n')

# ---- liberty ----
def lib(path, corner):
    mn = corner == 'fast'
    def val(pair): return pair[0] if mn else pair[1]
    def arc(rel, kind, d):
        return (f'      timing() {{ related_pin : "{rel}"; timing_type : {kind}; cell_rise(scalar) {{ values("{d:.3f}"); }} cell_fall(scalar) {{ values("{d:.3f}"); }}'
                f' rise_transition(scalar) {{ values("0.050"); }} fall_transition(scalar) {{ values("0.050"); }} }}\n')
    def chk(rel, kind, d):
        return f'      timing() {{ related_pin : "{rel}"; timing_type : {kind}; rise_constraint(scalar) {{ values("{d:.3f}"); }} fall_constraint(scalar) {{ values("{d:.3f}"); }} }}\n'
    o = [f'library (xc7sta_{corner}) {{\n  delay_model : table_lookup;\n  time_unit : "1ns";\n  capacitive_load_unit (1,pf);\n'
         '  voltage_unit : "1V"; current_unit : "1mA"; pulling_resistance_unit : "1kohm"; leakage_power_unit : "1nW";\n'
         '  nom_process : 1; nom_temperature : 25; nom_voltage : 1;\n'
         '  lu_table_template(scalar) { }\n'
         '  type (bus32) { base_type : array; data_type : bit; bit_width : 32; bit_from : 31; bit_to : 0; }\n'
         '  type (bus16) { base_type : array; data_type : bit; bit_width : 16; bit_from : 15; bit_to : 0; }\n'
         '  type (bus14) { base_type : array; data_type : bit; bit_width : 14; bit_from : 13; bit_to : 0; }\n'
         '  type (bus9) { base_type : array; data_type : bit; bit_width : 9; bit_from : 8; bit_to : 0; }\n'
         '  type (bus8) { base_type : array; data_type : bit; bit_width : 8; bit_from : 7; bit_to : 0; }\n'
         '  type (bus4) { base_type : array; data_type : bit; bit_width : 4; bit_from : 3; bit_to : 0; }\n'
         '  type (bus2) { base_type : array; data_type : bit; bit_width : 2; bit_from : 1; bit_to : 0; }\n']
    for n in range(1, 7):
        o.append(f'  cell (XLUT{n}) {{\n')
        for i in range(n): o.append(f'    pin (I{i}) {{ direction : input; }}\n')
        o.append('    pin (O) { direction : output; function : "' + '&'.join(f'I{i}' for i in range(n)) + '";\n')
        for i in range(n): o.append(arc(f'I{i}', 'combinational', val(LUT)))
        o.append('    }\n  }\n')
    for kind, async_ in (('XFF', False), ('XFFA', True)):
        o.append(f'  cell ({kind}) {{\n    ff (IQ, IQN) {{ clocked_on : "C"; next_state : "D"; }}\n')
        o.append('    pin (C) { direction : input; clock : true; }\n')
        o.append('    pin (D) { direction : input; ' + chk('C', 'setup_rising', FF_SETUP) + chk('C', 'hold_rising', FF_HOLD) + '}\n')
        o.append('    pin (CE) { direction : input; ' + chk('C', 'setup_rising', CE_SETUP) + chk('C', 'hold_rising', CE_HOLD) + '}\n')
        if async_:
            o.append('    pin (R) { direction : input; ' + arc('R', 'clear', val(CLKQ)) + '}\n')
        else:
            o.append('    pin (R) { direction : input; ' + chk('C', 'setup_rising', CE_SETUP) + chk('C', 'hold_rising', CE_HOLD) + '}\n')
        o.append('    pin (Q) { direction : output; function : "IQ"; ' + arc('C', 'rising_edge', val(CLKQ)) + '}\n  }\n')
    o.append('  cell (XCY) {\n    pin (S) { direction : input; }\n    pin (DI) { direction : input; }\n    pin (CI) { direction : input; }\n')
    o.append('    pin (CO) { direction : output; function : "(S&CI)|(!S&DI)"; ' + arc('S', 'combinational', val(MUXF)) + arc('DI', 'combinational', val(MUXF)) + arc('CI', 'combinational', val(CY)) + '}\n')
    o.append('    pin (XO) { direction : output; function : "S^CI"; ' + arc('S', 'combinational', val(MUXF)) + arc('CI', 'combinational', val(CY)) + '}\n  }\n')
    o.append('  cell (XINV) {\n    pin (I) { direction : input; }\n    pin (O) { direction : output; function : "!I"; ' + arc('I', 'combinational', val(INV)) + '}\n  }\n')
    o.append('  cell (XMUXF) {\n    pin (I0) { direction : input; }\n    pin (I1) { direction : input; }\n    pin (S) { direction : input; }\n')
    o.append('    pin (O) { direction : output; function : "(S&I1)|(!S&I0)"; ' + ''.join(arc(k, 'combinational', val(MUXF)) for k in ('I0', 'I1', 'S')) + '}\n  }\n')
    o.append('  cell (XMMCM) {\n    pin (LOCKED) { direction : output; }\n  }\n')
    for kind, bus in BUS.items():
        o.append(f'  cell ({kind}) {{\n')
        for pin in ('CLKARDCLK', 'CLKBWRCLK'): o.append(f'    pin ({pin}) {{ direction : input; clock : true; }}\n')
        def group(pin):
            for k in ('DIP', 'DI', 'ADDR', 'WE', 'EN', 'RST', 'REGCE'):
                if pin.startswith(k): return k
            return 'EN'
        for pin in RAM_SCALAR_IN:
            if pin.startswith('CLK'): continue
            clk = 'CLKBWRCLK' if pin.endswith(('B', 'BWREN', 'BWRCLK')) or pin in ('RSTRAMB', 'REGCEB', 'RSTREGB') else 'CLKARDCLK'
            g = group(pin)
            o.append(f'    pin ({pin}) {{ direction : input; ' + chk(clk, 'setup_rising', BRAM_SETUP[g]) + chk(clk, 'hold_rising', BRAM_HOLD[g]) + '}\n')
        for pin in RAM_SCALAR_OUT: o.append(f'    pin ({pin}) {{ direction : output; }}\n')
        for pin, w in bus.items():
            o.append(f'    bus ({pin}) {{ bus_type : bus{w}; ')
            if pin.startswith('DO') or pin in ('ECCPARITY', 'RDADDRECC'):
                clk = 'CLKBWRCLK' if pin.startswith('DOB') or pin.startswith('DOPB') else 'CLKARDCLK'
                o.append('direction : output; ' + arc(clk, 'rising_edge', val(BRAM_CLKQ)) + '}\n')
            else:
                clk = 'CLKBWRCLK' if pin in ('ADDRBWRADDR', 'DIBDI', 'DIPBDIP', 'WEBWE') else 'CLKARDCLK'
                # DIADI/DIPADIP are written on port A's clock in TDP mode
                g = group(pin)
                o.append('direction : input; ' + chk(clk, 'setup_rising', BRAM_SETUP[g]) + chk(clk, 'hold_rising', BRAM_HOLD[g]) + '}\n')
        o.append('  }\n')
    o.append('}\n')
    open(path, 'w').write(''.join(o))
lib(os.path.join(outdir, 'fast.lib'), 'fast')
lib(os.path.join(outdir, 'slow.lib'), 'slow')

# ---- SDF: interconnect per driver -> load ----
def cal(d):
    return (CAL_MIN[0] * d[0] + CAL_MIN[1], CAL_MAX[0] * d[1] + CAL_MAX[1])
with open(os.path.join(outdir, 'delays.sdf'), 'w') as f:
    f.write('(DELAYFILE\n (SDFVERSION "3.0")\n (DESIGN "fabric_sta")\n (TIMESCALE 1ns)\n (CELL\n  (CELLTYPE "fabric_sta")\n  (INSTANCE)\n  (DELAY\n   (ABSOLUTE\n')
    n = 0
    for net, ls in loads.items():
        drv = drivers.get(net)
        if not drv: continue
        for inst, pin, wire in ls:
            if wire is None or wire not in src_of:
                continue                      # an internal connection, or the root itself: no interconnect
            dmin, dmax = cal(wire_delay(wire))
            f.write(f'    (INTERCONNECT {drv} {inst}/{pin} ({dmin:.3f}:{dmax:.3f}:{dmax:.3f}))\n'); n += 1
    f.write('   )\n  )\n )\n)\n')
print(f'{n} interconnect delays', file=sys.stderr)

# ---- SDC: a clock on every clock root ----
# A clock pin's net traces back through the extractor's route-through LUTs
# (nextpnr takes an MMCM output to its BUFG through the fabric, LUT and all)
# to the port the clock enters on.
cell_by_out = {}
for kind, name, pn in cells:
    if kind.startswith('XLUT'): cell_by_out[pn['O']] = (kind, name, pn)
def clock_root(net):
    for _ in range(8):
        if net in inputs: return net
        c = cell_by_out.get(net)
        if not c: return None
        ins = [v for k, v in c[2].items() if k.startswith('I')]
        if len(ins) != 1: return None
        net = ins[0]
    return None
clock_roots = defaultdict(int)
for kind, name, pn in cells:
    for k in ('C', 'CLKARDCLK', 'CLKBWRCLK'):
        v = pn.get(k)
        r = clock_root(v) if v else None
        if r: clock_roots[r] += 1
# BUFG sites for names: tile BOT holds Y0..15, TOP Y16..31
site_period = {}
if placement:
    for cn, pl in placement.items():
        if pl['type'] == 'BUFGCTRL':
            for k, per in clocks.items():
                if k in cn or k == pl['site']: site_period[pl['site']] = (cn, per)
with open(os.path.join(outdir, 'design.sdc'), 'w') as f:
    names = []
    for root, cnt in sorted(clock_roots.items(), key=lambda kv: -kv[1]):
        per = None; label = root
        m = re.match(r'CLK_BUFG_(BOT|TOP)_R_X\d+Y\d+_CLK_BUFG_BUFGCTRL(\d+)_O', root)
        if m:
            site = f"BUFGCTRL_X0Y{int(m.group(2)) + (16 if m.group(1) == 'TOP' else 0)}"
            if site in site_period: label, per = site_period[site]
        for k, p in clocks.items():
            if per is None and k in root: per = p
        if per is None:
            per = 8.0; print(f'clock root {root} ({cnt} loads): no period given, assuming 8 ns', file=sys.stderr)
        cname = san(label)
        names.append(cname)
        f.write(f'create_clock -name {cname} -period {per:.3f} [get_ports {root}]\n')
    f.write('set_clock_groups -asynchronous ' + ' '.join(f'-group {{{n}}}' for n in names) + '\n')
    # The global clock tree is balanced hardware the database's per-class pip
    # delays do not describe, so the clocks are ideal and skew is a budget.
    f.write('set_clock_uncertainty -setup 0.25 [all_clocks]\nset_clock_uncertainty -hold 0.25 [all_clocks]\n')
    for n in inputs:
        if n not in clock_roots: f.write(f'set_input_delay 0 [get_ports {n}]\n')
with open(os.path.join(outdir, 'run.tcl'), 'w') as f:
    f.write(f'''read_liberty -min {outdir}/fast.lib
read_liberty -max {outdir}/slow.lib
read_verilog {outdir}/netlist.v
link_design fabric_sta
read_sdf {outdir}/delays.sdf
read_sdc {outdir}/design.sdc
puts "=== setup (max)"
report_checks -path_delay max -group_path_count 3 -format full_clock_expanded
puts "=== hold (min)"
report_checks -path_delay min -group_path_count 3 -format full_clock_expanded
puts "=== summary"
report_tns
report_wns
report_clock_skew
puts "=== worst hold endpoints"
report_checks -path_delay min -group_path_count 1 -endpoint_path_count 1 -format end -unique_paths_to_endpoint
''')
print('wrote', outdir, file=sys.stderr)
