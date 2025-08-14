import React, { useEffect, useMemo, useRef, useState } from "react";
import { motion } from "framer-motion";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Switch } from "@/components/ui/switch";
import { Input } from "@/components/ui/input";
import { Badge } from "@/components/ui/badge";
import { Play, Pause, RefreshCw, MapPin, Gauge, Car, LayoutGrid } from "lucide-react";

// --- Utilities
const rand = (min, max) => min + Math.random() * (max - min);
const uid = () => Math.random().toString(36).slice(2, 9);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

// --- Queue model helpers
const exp = (ratePerMin) => (ratePerMin <= 0 ? Infinity : -Math.log(1 - Math.random()) / ratePerMin);
const predictedQueueTime = (q, rate, servers) => (rate <= 0 || servers <= 0 ? Infinity : q / (rate * servers));

const chooseBestLane = (sys, isMobile) => {
  const lanes = ["A", "B"];
  const mobileFactor = isMobile ? 0.55 : 1.0;
  let best = lanes[0];
  let bestTime = Infinity;
  for (const L of lanes) {
    const tOrder = predictedQueueTime(sys.queues.order[L].length, sys.params.orderRate, sys.params.orderServers[L]);
    const tPay = predictedQueueTime(sys.queues.pay.length, sys.params.payRate, sys.params.payServers);
    const tPickup = predictedQueueTime(sys.queues.pickup.length, sys.params.pickupRate, sys.params.pickupServers);
    const total = tOrder * mobileFactor + tPay + tPickup;
    if (total < bestTime) { bestTime = total; best = L; }
  }
  return { lane: best, eta: bestTime };
};

function chooseParkingSpot(spots, opts) {
  const { entrance = { x: 6, y: 70 }, w = { dist: 1, exit: 0.6, cong: 0.8, angle: 0.2 } } = opts || {};
  let best = null, bestScore = Infinity;
  for (const s of spots) {
    if (s.occupied || s.reserved) continue;
    const dx = s.x - entrance.x, dy = s.y - entrance.y;
    const dist = Math.hypot(dx, dy);
    const score = w.dist * dist + w.exit * s.exitFriction + w.cong * s.localCongestion + w.angle * (s.backIn ? 0.7 : 0);
    if (score < bestScore) { bestScore = score; best = s; }
  }
  return best;
}

function rebalanceServers(sys) {
  const util = (q, rate, s) => (s > 0 ? q / (rate * s + 1e-6) : Infinity);
  const pressure = {
    orderA: util(sys.queues.order.A.length, sys.params.orderRate, sys.params.orderServers.A),
    orderB: util(sys.queues.order.B.length, sys.params.orderRate, sys.params.orderServers.B),
    pay: util(sys.queues.pay.length, sys.params.payRate, sys.params.payServers),
    pickup: util(sys.queues.pickup.length, sys.params.pickupRate, sys.params.pickupServers),
  };
  const entries = Object.entries(pressure).sort((a, b) => b[1] - a[1]);
  const hottest = entries[0][0];
  const stages = {
    orderA: () => ({ get: () => sys.params.orderServers.A, set: (v) => (sys.params.orderServers.A = v), min: 1 }),
    orderB: () => ({ get: () => sys.params.orderServers.B, set: (v) => (sys.params.orderServers.B = v), min: 1 }),
    pay: () => ({ get: () => sys.params.payServers, set: (v) => (sys.params.payServers = v), min: 1 }),
    pickup: () => ({ get: () => sys.params.pickupServers, set: (v) => (sys.params.pickupServers = v), min: 1 }),
  };
  for (const [name] of entries.slice().reverse()) {
    if (name === hottest) continue;
    const s = stages[name]();
    if (s.get() > s.min) {
      s.set(s.get() - 1);
      const h = stages[hottest]();
      h.set(h.get() + 1);
      return { from: name, to: hottest };
    }
  }
  return null;
}

// --- Erlang C helpers
function erlangC(lam, mu, s) {
  if (s <= 0 || mu <= 0) return 1;
  const rho = lam / (s * mu);
  if (rho >= 1) return 1;
  let sum = 0;
  for (let k = 0; k < s; k++) {
    sum += Math.pow(lam / mu, k) / fact(k);
  }
  const ps = (Math.pow(lam / mu, s) / (fact(s) * (1 - rho))) * (1 / (sum + (Math.pow(lam / mu, s) / (fact(s) * (1 - rho)))));
  return ps;
}
function fact(n) { let r = 1; for (let i = 2; i <= n; i++) r *= i; return r; }
function expectedWaitMinutes(lam, mu, s) {
  if (s <= 0 || mu <= 0) return Infinity;
  const C = erlangC(lam, mu, s);
  const rho = lam / (s * mu);
  if (rho >= 1) return Infinity;
  return (C / (s * mu - lam));
}

// --- Simulation hook
function useSimulation() {
  const [running, setRunning] = useState(false);
  const [now, setNow] = useState(0);
  const [params, setParams] = useState({
    arrivalRate: 36,
    mobileShare: 0.35,
    divertThresholdMin: 7,
    orderRate: 0.8,
    payRate: 1.3,
    pickupRate: 1.0,
    orderServers: { A: 1, B: 1 },
    payServers: 1,
    pickupServers: 1,
    autoRebalance: true,
  });
  const [queues, setQueues] = useState({ order: { A: [], B: [] }, pay: [], pickup: [], curbside: [] });
  const [spots, setSpots] = useState(() => generateSpots());
  const metrics = useRef({ arrivals: 0, served: 0, parked: 0, avgWait: 0, maxWip: 0, history: [] });

  const nextArrival = useRef(exp(params.arrivalRate / 60));
  const orderClock = useRef({ A: 0, B: 0 });
  const payClock = useRef(0);
  const pickupClock = useRef(0);

  const tickMs = 120;
  const minutesPerTick = 0.08;

  useEffect(() => {
    if (!running) return;
    const id = setInterval(() => step(minutesPerTick), tickMs);
    return () => clearInterval(id);
  }, [running, params]);

  function step(dt) {
    setNow((t) => t + dt);
    const sys = { queues, params };

    // Arrivals
    nextArrival.current -= dt;
    while (nextArrival.current <= 0) {
      const car = { id: uid(), arrival: now, isMobile: Math.random() < params.mobileShare, progress: {} };
      metrics.current.arrivals++;
      const { eta, lane } = chooseBestLane(sys, car.isMobile);
      if (eta > params.divertThresholdMin) {
        const spot = chooseParkingSpot(spots, { entrance: { x: 6, y: 70 } });
        if (spot) {
          spot.occupied = true; car.parkingSpotId = spot.id; car.state = "curbside"; queues.curbside.push(car); metrics.current.parked++;
        } else {
          car.lane = lane; queues.order[lane].push(car);
        }
      } else {
        car.lane = lane; queues.order[lane].push(car);
      }
      nextArrival.current += exp(params.arrivalRate / 60);
    }

    // Order service
    for (const L of ["A", "B"]) {
      if (queues.order[L].length > 0 && params.orderServers[L] > 0) {
        orderClock.current[L] -= dt * params.orderServers[L];
        if (orderClock.current[L] <= 0) {
          const car = queues.order[L].shift();
          car.progress.order = now; queues.pay.push(car); orderClock.current[L] = 1 / params.orderRate;
        }
      } else {
        orderClock.current[L] = Math.max(orderClock.current[L], 1 / params.orderRate);
      }
    }

    // Pay
    if (queues.pay.length > 0 && params.payServers > 0) {
      payClock.current -= dt * params.payServers;
      if (payClock.current <= 0) {
        const car = queues.pay.shift(); car.progress.pay = now; queues.pickup.push(car); payClock.current = 1 / params.payRate; }
    } else { payClock.current = Math.max(payClock.current, 1 / params.payRate); }

    // Pickup
    if (queues.pickup.length > 0 && params.pickupServers > 0) {
      pickupClock.current -= dt * params.pickupServers;
      if (pickupClock.current <= 0) {
        const car = queues.pickup.shift(); car.progress.pickup = now; metrics.current.served++;
        const w = now - car.arrival; const m = metrics.current; m.avgWait = (m.avgWait * (m.served - 1) + w) / m.served; pickupClock.current = 1 / params.pickupRate; }
    } else { pickupClock.current = Math.max(pickupClock.current, 1 / params.pickupRate); }

    // Curbside completions
    for (let i = queues.curbside.length - 1; i >= 0; i--) {
      const car = queues.curbside[i]; if (!car.readyAt) car.readyAt = car.arrival + rand(4, 10);
      if (now >= car.readyAt) { const s = spots.find((x) => x.id === car.parkingSpotId); if (s) s.occupied = false; queues.curbside.splice(i, 1);
        metrics.current.served++; const w = now - car.arrival; const m = metrics.current; m.avgWait = (m.avgWait * (m.served - 1) + w) / m.served; }
    }

    const wip = queues.order.A.length + queues.order.B.length + queues.pay.length + queues.pickup.length + queues.curbside.length;
    metrics.current.maxWip = Math.max(metrics.current.maxWip, wip);
    metrics.current.history.push({ t: now, wip, wait: metrics.current.avgWait });

    if (params.autoRebalance && Math.random() < 0.05) { rebalanceServers({ queues, params }); }

    setQueues({ ...queues }); setSpots([...spots]);
  }

  function reset() {
    setQueues({ order: { A: [], B: [] }, pay: [], pickup: [], curbside: [] });
    setSpots(generateSpots());
    metrics.current = { arrivals: 0, served: 0, parked: 0, avgWait: 0, maxWip: 0, history: [] };
    orderClock.current = { A: 0, B: 0 }; payClock.current = 0; pickupClock.current = 0; nextArrival.current = exp(params.arrivalRate / 60);
    setNow(0);
  }

  return { running, setRunning, now, params, setParams, queues, spots, metrics, reset };
}

function generateSpots() {
  const arr = []; let id = 1;
  for (let r = 0; r < 4; r++) {
    for (let c = 0; c < 14; c++) {
      arr.push({ id: `S${id++}`, x: 6 + c * 6, y: 60 + r * 8, occupied: Math.random() < 0.2, reserved: c < 2 && r === 0, exitFriction: (r + 1) * 0.2 + (c > 10 ? 0.8 : 0.2), localCongestion: Math.random() * 0.6, backIn: Math.random() < 0.25 });
    }
  }
  return arr;
}

// Canvas Map component
function CanvasMap({ queues, spots }) {
  const ref = useRef(null);
  const animRef = useRef(0);
  const carsRef = useRef([]);
  const lastRef = useRef(performance.now());

  const lanes = useMemo(() => {
    const loop = [
      [0.06, 0.85], [0.12, 0.7], [0.25, 0.62], [0.5, 0.58], [0.78, 0.62], [0.92, 0.5], [0.8, 0.36], [0.52, 0.3], [0.24, 0.36], [0.1, 0.52], [0.06, 0.85]
    ];
    const inner = loop.map(([x, y]) => [x + 0.03, y - 0.04]);
    const payBay = [[0.88, 0.46], [0.96, 0.46]];
    const pickupBay = [[0.84, 0.40], [0.94, 0.40]];
    return { A: loop, B: inner, payBay, pickupBay };
  }, []);

  useEffect(() => {
    const total = 34;
    const arr = [];
    for (let i = 0; i < total; i++) {
      const lane = i % 2 === 0 ? "A" : "B";
      arr.push({ id: uid(), lane, seg: 0, t: Math.random(), speed: rand(0.12, 0.22), color: lane === "A" ? "#22c55e" : "#22d3ee" });
    }
    carsRef.current = arr;
  }, []);

  useEffect(() => {
    const canvas = ref.current;
    if (!canvas) return;
    const ctx = canvas.getContext("2d");

    function resize() {
      const dpr = window.devicePixelRatio || 1;
      const rect = canvas.getBoundingClientRect();
      canvas.width = Math.floor(rect.width * dpr);
      canvas.height = Math.floor(rect.height * dpr);
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    }
    resize();
    const ro = new ResizeObserver(resize); ro.observe(canvas);

    function lerp(a, b, t) { return a + (b - a) * t; }
    function segPoint(poly, seg, t) {
      const a = poly[seg]; const b = poly[(seg + 1) % poly.length];
      return [lerp(a[0], b[0], t), lerp(a[1], b[1], t)];
    }

    function drawRoad() {
      const { width, height } = canvas.getBoundingClientRect();
      const grd = ctx.createLinearGradient(0, 0, width, height);
      grd.addColorStop(0, "#0b1220");
      grd.addColorStop(1, "#0a0f1a");
      ctx.fillStyle = grd; ctx.fillRect(0, 0, width, height);

      ctx.fillStyle = "#e11d48";
      roundRect(ctx, width * 0.39, height * 0.34, width * 0.22, height * 0.18, 14, true, false);
      ctx.strokeStyle = "rgba(251,113,133,0.5)"; ctx.lineWidth = 4; roundRect(ctx, width * 0.39, height * 0.34, width * 0.22, height * 0.18, 14, false, true);

      function drawLane(poly, color) {
        ctx.strokeStyle = color; ctx.lineWidth = 18; ctx.lineCap = "round"; ctx.lineJoin = "round";
        ctx.beginPath();
        poly.forEach(([x, y], i) => { const px = x * width, py = y * height; i === 0 ? ctx.moveTo(px, py) : ctx.lineTo(px, py); });
        ctx.stroke();
        ctx.setLineDash([14, 14]); ctx.lineWidth = 2; ctx.strokeStyle = "rgba(255,255,255,0.6)";
        ctx.stroke(); ctx.setLineDash([]);
      }
      drawLane(lanes.A, "rgba(16,185,129,0.25)");
      drawLane(lanes.B, "rgba(34,211,238,0.25)");

      ctx.lineWidth = 10; ctx.strokeStyle = "rgba(250,204,21,0.45)"; pathLine(lanes.payBay);
      ctx.strokeStyle = "rgba(167,139,250,0.45)"; pathLine(lanes.pickupBay);

      for (const s of spots) {
        const x = s.x / 100 * width, y = s.y / 100 * height; const w = 28, h = 40;
        ctx.lineWidth = 2; ctx.strokeStyle = s.reserved ? "#38bdf8" : "rgba(148,163,184,0.5)";
        ctx.fillStyle = s.occupied ? "#e5e7eb" : "rgba(2,6,23,0.3)";
        roundRect(ctx, x, y, w, h, 6, true, true);
      }

      ctx.font = "12px Inter, system-ui, sans-serif"; ctx.fillStyle = "#e2e8f0";
      ctx.fillText(`Curbside: ${queues.curbside.length}`, 12, height - 12);
    }

    function pathLine(poly) {
      const { width, height } = canvas.getBoundingClientRect();
      ctx.beginPath();
      poly.forEach(([x, y], i) => { const px = x * width, py = y * height; i === 0 ? ctx.moveTo(px, py) : ctx.lineTo(px, py); });
      ctx.stroke();
    }

    function roundRect(ctx, x, y, w, h, r, fill = true, stroke = true) {
      if (w < 2 * r) r = w / 2; if (h < 2 * r) r = h / 2;
      ctx.beginPath(); ctx.moveTo(x + r, y);
      ctx.arcTo(x + w, y, x + w, y + h, r);
      ctx.arcTo(x + w, y + h, x, y + h, r);
      ctx.arcTo(x, y + h, x, y, r);
      ctx.arcTo(x, y, x + w, y, r); ctx.closePath();
      if (fill) ctx.fill(); if (stroke) ctx.stroke();
    }

    function stepCars(dt) {
      const { width, height } = canvas.getBoundingClientRect();
      for (const c of carsRef.current) {
        const path = c.lane === "A" ? lanes.A : lanes.B;
        c.t += dt * c.speed;
        while (c.t >= 1) { c.t -= 1; c.seg = (c.seg + 1) % path.length; }
        if (Math.random() < 0.02) c.speed = clamp(c.speed + rand(-0.02, 0.02), 0.08, 0.28);
        const [x, y] = segPoint(path, c.seg, c.t);
        const px = x * width, py = y * height; const w = 14, h = 10;
        ctx.save();
        ctx.translate(px, py);
        ctx.fillStyle = c.color;
        ctx.shadowColor = c.color; ctx.shadowBlur = 8;
        roundRect(ctx, -w/2, -h/2, w, h, 3, true, false);
        ctx.restore();
      }

      function drawQueueDots(n, baseX, baseY, color) {
        for (let i = 0; i < n; i++) {
          const off = i * 12;
          ctx.fillStyle = color; ctx.shadowColor = color; ctx.shadowBlur = 6;
          ctx.beginPath(); ctx.arc(baseX - off, baseY, 4 + (i===0?1:0), 0, Math.PI*2); ctx.fill();
        }
      }
      drawQueueDots(queues.pay.length, width * 0.95, height * 0.46, "#fde047");
      drawQueueDots(queues.pickup.length, width * 0.93, height * 0.40, "#c4b5fd");

      pulse(width * lanes.A[0][0], height * lanes.A[0][1], "#22c55e");
      pulse(width * lanes.B[0][0], height * lanes.B[0][1], "#22d3ee");

      function pulse(x, y, color) {
        const t = (performance.now() % 1000) / 1000;
        const r = 6 + Math.sin(t * Math.PI * 2) * 2;
        ctx.beginPath(); ctx.fillStyle = color; ctx.globalAlpha = 0.8; ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill(); ctx.globalAlpha = 1;
      }
    }

    function frame(ts) {
      const dt = Math.min(0.05, (ts - lastRef.current) / 1000);
      lastRef.current = ts;
      drawRoad();
      stepCars(dt);
      animRef.current = requestAnimationFrame(frame);
    }

    animRef.current = requestAnimationFrame(frame);
    return () => { cancelAnimationFrame(animRef.current); ro.disconnect(); };
  }, [lanes, spots, queues]);

  return (
    <div className="relative w-full h-[560px] rounded-3xl overflow-hidden border-2 border-slate-700 shadow-2xl">
      <canvas ref={ref} className="absolute inset-0 w-full h-full" />
      <div className="absolute left-4 top-4 px-2 py-1 rounded-md bg-black/30 backdrop-blur text-xs text-slate-200">
        <span className="mr-2">🟢 Lane A</span>
        <span className="mr-2">🔵 Lane B</span>
        <span className="mr-2">🟡 Pay</span>
        <span>🟣 Pickup</span>
      </div>
    </div>
  );
}

function Stat({ label, value, unit }) {
  return (
    <div className="p-4 rounded-2xl bg-slate-900/90 border border-slate-600/60 shadow-xl">
      <div className="text-slate-300 text-xs uppercase tracking-wider">{label}</div>
      <div className="mt-1 flex items-end gap-1">
        <div className="text-3xl font-bold text-amber-300 drop-shadow">{value}</div>
        {unit && <div className="text-slate-400 text-xs mb-1">{unit}</div>}
      </div>
    </div>
  );
}

function Control({ label, value, onChange, min = 0, max = 1, step = 0.01 }) {
  return (
    <div className="p-3 rounded-xl bg-slate-900/80 border border-slate-700 space-y-2">
      <div className="text-sm text-slate-200 font-medium">{label}</div>
      <div className="flex items-center gap-3">
        <input type="range" min={min} max={max} step={step} value={value} onChange={(e) => onChange(parseFloat(e.target.value))} className="w-full accent-amber-400" />
        <Input value={typeof value === 'number' ? value : ''} onChange={() => {}} readOnly className="w-24 h-8 text-right" />
      </div>
    </div>
  );
}

function Legend() {
  return (
    <div className="flex flex-wrap items-center gap-2 text-xs">
      <Badge className="bg-emerald-500 text-black">Lane A</Badge>
      <Badge className="bg-cyan-400 text-black">Lane B</Badge>
      <Badge className="bg-yellow-400 text-black">Pay</Badge>
      <Badge className="bg-violet-400 text-black">Pickup</Badge>
      <Badge className="bg-sky-400 text-black">Reserved</Badge>
      <Badge variant="secondary" className="bg-white text-black">Occupied</Badge>
    </div>
  );
}

export default function App() {
  const sim = useSimulation();
  const [hc, setHc] = useState(true);

  const m = sim.metrics.current;
  const kpis = useMemo(() => ([
    { label: "Arrivals", value: m.arrivals },
    { label: "Served", value: m.served },
    { label: "Parked", value: m.parked },
    { label: "Avg Wait", value: m.avgWait.toFixed(1), unit: "min" },
    { label: "Max WIP", value: m.maxWip },
  ]), [sim.queues]);

  const etaOrderA = expectedWaitMinutes(sim.queues.order.A.length + 1, sim.params.orderRate, sim.params.orderServers.A);
  const etaOrderB = expectedWaitMinutes(sim.queues.order.B.length + 1, sim.params.orderRate, sim.params.orderServers.B);
  const etaPay = expectedWaitMinutes(sim.queues.pay.length + 1, sim.params.payRate, sim.params.payServers);
  const etaPickup = expectedWaitMinutes(sim.queues.pickup.length + 1, sim.params.pickupRate, sim.params.pickupServers);
  const etaA = (etaOrderA || 0) + (etaPay || 0) + (etaPickup || 0);
  const etaB = (etaOrderB || 0) + (etaPay || 0) + (etaPickup || 0);
  const advise = Math.min(etaA, etaB) > sim.params.divertThresholdMin ? "Divert to curbside" : `Use lane ${etaA < etaB ? 'A' : 'B'}`;

  return (
    <div className={`min-h-screen ${hc ? 'bg-slate-950' : 'bg-white'} p-6 text-white`}>
      <div className="max-w-7xl mx-auto space-y-6">
        <div className="flex flex-wrap items-center justify-between gap-4">
          <div className="flex items-center gap-3">
            <MapPin className="text-amber-400" />
            <h1 className="text-3xl md:text-4xl font-extrabold tracking-tight text-amber-300 drop-shadow">Drive‑Thru Optimizer</h1>
          </div>
          <div className="flex items-center gap-2">
            <Button onClick={() => sim.setRunning((r) => !r)} className="rounded-2xl bg-emerald-500 text-black hover:bg-emerald-400">
              {sim.running ? <Pause className="mr-2 h-4 w-4" /> : <Play className="mr-2 h-4 w-4" />} {sim.running ? "Pause" : "Start"}
            </Button>
            <Button variant="secondary" onClick={sim.reset} className="rounded-2xl border border-slate-600"><RefreshCw className="mr-2 h-4 w-4" />Reset</Button>
            <div className="flex items-center gap-2 ml-3">
              <span className="text-xs text-slate-300">High Contrast</span>
              <Switch checked={hc} onCheckedChange={setHc} />
            </div>
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
          <Card className="lg:col-span-2 bg-slate-900/70 border-slate-700">
            <CardHeader>
              <CardTitle className="flex items-center gap-2 text-amber-300"><LayoutGrid className="h-5 w-5" /> Site Map</CardTitle>
            </CardHeader>
            <CardContent>
              <CanvasMap queues={sim.queues} spots={sim.spots} />
              <div className="flex items-center gap-3 mt-4 text-xs text-slate-400">
                <Legend />
                <span className="ml-auto">Animation is synthetic for realism; queues and bays reflect live counts.</span>
              </div>
            </CardContent>
          </Card>

          <Card className="bg-slate-900/70 border-slate-700">
            <CardHeader>
              <CardTitle className="flex items-center gap-2 text-amber-300"><Gauge className="h-5 w-5" /> KPIs</CardTitle>
            </CardHeader>
            <CardContent className="grid grid-cols-2 gap-3">
              {kpis.map((k) => (
                <Stat key={k.label} {...k} />
              ))}
              <div className="col-span-2 text-xs text-slate-400">Time: {sim.now.toFixed(1)} min</div>
            </CardContent>
          </Card>
        </div>

        <Card className="bg-slate-900/70 border-slate-700">
          <CardHeader>
            <CardTitle className="text-amber-300">Predicted ETA (now)</CardTitle>
          </CardHeader>
          <CardContent className="grid grid-cols-1 md:grid-cols-3 gap-4">
            <div className="p-4 rounded-2xl bg-slate-900/80 border border-slate-700">
              <div className="text-slate-300 text-xs mb-1">Lane A</div>
              <div className="text-2xl font-bold text-emerald-400">{isFinite(etaA) ? etaA.toFixed(1) : '∞'}<span className="text-xs ml-1">min</span></div>
            </div>
            <div className="p-4 rounded-2xl bg-slate-900/80 border border-slate-700">
              <div className="text-slate-300 text-xs mb-1">Lane B</div>
              <div className="text-2xl font-bold text-cyan-300">{isFinite(etaB) ? etaB.toFixed(1) : '∞'}<span className="text-xs ml-1">min</span></div>
            </div>
            <div className="p-4 rounded-2xl bg-slate-900/80 border border-slate-700 flex items-center justify-between">
              <div>
                <div className="text-slate-300 text-xs mb-1">Advisor</div>
                <div className="text-lg font-semibold text-amber-300">{advise}</div>
              </div>
              <Badge className="bg-amber-400 text-black">Threshold {sim.params.divertThresholdMin}m</Badge>
            </div>
          </CardContent>
        </Card>

        <Card className="bg-slate-900/70 border-slate-700">
          <CardHeader>
            <CardTitle className="flex items-center gap-2 text-amber-300"><Car className="h-5 w-5" /> Controls</CardTitle>
          </CardHeader>
          <CardContent className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
            <Control label="Arrivals/hr" value={sim.params.arrivalRate} onChange={(v)=> sim.setParams(p=>({...p, arrivalRate: v}))} min={1} max={120} step={1} />
            <Control label="Mobile share" value={sim.params.mobileShare} onChange={(v)=> sim.setParams(p=>({...p, mobileShare: v}))} min={0} max={1} step={0.05} />
            <Control label="Divert threshold (min)" value={sim.params.divertThresholdMin} onChange={(v)=> sim.setParams(p=>({...p, divertThresholdMin: v}))} min={2} max={20} step={0.5} />
            <Control label="Order rate /server (1/min)" value={sim.params.orderRate} onChange={(v)=> sim.setParams(p=>({...p, orderRate: v}))} min={0.2} max={2} step={0.05} />
            <Control label="Pay rate /server (1/min)" value={sim.params.payRate} onChange={(v)=> sim.setParams(p=>({...p, payRate: v}))} min={0.2} max={3} step={0.05} />
            <Control label="Pickup rate /server (1/min)" value={sim.params.pickupRate} onChange={(v)=> sim.setParams(p=>({...p, pickupRate: v}))} min={0.2} max={3} step={0.05} />
            <Control label="Order servers A" value={sim.params.orderServers.A} onChange={(v)=> sim.setParams(p=>({...p, orderServers:{...p.orderServers, A: Math.round(v)}}))} min={1} max={3} step={1} />
            <Control label="Order servers B" value={sim.params.orderServers.B} onChange={(v)=> sim.setParams(p=>({...p, orderServers:{...p.orderServers, B: Math.round(v)}}))} min={1} max={3} step={1} />
            <Control label="Pay servers" value={sim.params.payServers} onChange={(v)=> sim.setParams(p=>({...p, payServers: Math.round(v)}))} min={1} max={3} step={1} />
            <Control label="Pickup servers" value={sim.params.pickupServers} onChange={(v)=> sim.setParams(p=>({...p, pickupServers: Math.round(v)}))} min={1} max={3} step={1} />
            <div className="p-3 rounded-xl bg-slate-900/80 border border-slate-700 flex items-center justify-between">
              <div>
                <div className="text-sm text-slate-200 font-medium">Auto staff rebalance</div>
                <div className="text-xs text-slate-400">Shift a server to the current bottleneck.</div>
              </div>
              <Switch checked={sim.params.autoRebalance} onCheckedChange={(v)=> sim.setParams(p=>({...p, autoRebalance: v}))} />
            </div>
          </CardContent>
        </Card>
      </div>
    </div>
  );
}
