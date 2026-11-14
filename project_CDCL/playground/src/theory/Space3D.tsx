import { useEffect, useRef } from "react";
import * as THREE from "three";
import { OrbitControls } from "three/examples/jsm/controls/OrbitControls.js";
import { num } from "./linear";
import type { Frame, LiaModel } from "./liaModel";

type V3 = [number, number, number];
type Face = V3[];

const COLOR = {
  space: 0x2f9e44,
  out: 0xd63939,
  line: 0x4b5563,
  fresh: 0x2f5bd3,
  derived: 0x7b3fc4,
  blame: 0xc92a2a,
  point: 0xf08c00,
  box: 0xb8b2a6,
  ink: "#1f2937",
};

/**
 * One frame of an LIA check with three variables: each constraint is a plane,
 * the side it rules out is a transparent red block (darker where several
 * overlap), and the green solid is what every constraint allows.
 */
export function Space3D({ model, frame }: { model: LiaModel; frame: Frame }) {
  const host = useRef<HTMLDivElement>(null);
  const ctx = useRef<{ renderer: THREE.WebGLRenderer; scene: THREE.Scene; camera: THREE.PerspectiveCamera; controls: OrbitControls; root: THREE.Group } | null>(null);

  // renderer, camera and controls live as long as the component
  useEffect(() => {
    const el = host.current!;
    const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
    renderer.setPixelRatio(window.devicePixelRatio);
    el.appendChild(renderer.domElement);
    const scene = new THREE.Scene();
    scene.add(new THREE.AmbientLight(0xffffff, 1.6));
    const sun = new THREE.DirectionalLight(0xffffff, 1.4);
    sun.position.set(2, -3, 4);
    scene.add(sun);
    const camera = new THREE.PerspectiveCamera(38, 1, 0.01, 100);
    camera.up.set(0, 0, 1);
    const controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.enableZoom = false; // the wheel scrolls the page; use the buttons
    const root = new THREE.Group();
    scene.add(root);
    ctx.current = { renderer, scene, camera, controls, root };
    const size = () => {
      const w = el.clientWidth || 560;
      const h = 440;
      renderer.setSize(w, h);
      camera.aspect = w / h;
      camera.updateProjectionMatrix();
    };
    size();
    const ro = new ResizeObserver(size);
    ro.observe(el);
    let raf = 0;
    const loop = () => {
      controls.update();
      renderer.render(scene, camera);
      raf = requestAnimationFrame(loop);
    };
    loop();
    return () => {
      cancelAnimationFrame(raf);
      ro.disconnect();
      clear(root);
      controls.dispose();
      renderer.dispose();
      el.removeChild(renderer.domElement);
      ctx.current = null;
    };
  }, []);

  // a new check: put the camera back, far enough for the whole box to fit
  useEffect(() => {
    const c = ctx.current;
    if (!c) return;
    const fit = 2.1 / Math.tan((c.camera.fov * Math.PI) / 360) / Math.min(1, c.camera.aspect);
    c.camera.position.set(0.55, -0.72, 0.42).normalize().multiplyScalar(fit);
    c.controls.target.set(0, 0, 0);
    c.controls.update();
  }, [model]);

  // the scene for this frame
  useEffect(() => {
    const c = ctx.current;
    if (c) draw(c.root, model, frame);
  }, [model, frame]);

  const zoom = (f: number) => {
    const c = ctx.current;
    if (!c) return;
    c.camera.position.sub(c.controls.target).multiplyScalar(f).add(c.controls.target);
  };
  const empty = frame.drawn.length > 0 && region(model, frame).length === 0;

  return (
    <div className="space3d" ref={host}>
      {empty && <div className="empty-overlay">no point is left</div>}
      <div className="space3d-tools">
        <button className="ghost small" onClick={() => zoom(0.8)} aria-label="zoom in">+</button>
        <button className="ghost small" onClick={() => zoom(1.25)} aria-label="zoom out">−</button>
      </div>
      <p className="space3d-hint">drag to turn the picture</p>
    </div>
  );
}

// ---------------------------------------------------------------- geometry

const dot = (a: V3, b: V3) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const sub = (a: V3, b: V3): V3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const cross = (a: V3, b: V3): V3 => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const norm = (a: V3): V3 => {
  const l = Math.hypot(...a) || 1;
  return [a[0] / l, a[1] / l, a[2] / l];
};

function boxFaces(b: [number, number][]): Face[] {
  const [[x0, x1], [y0, y1], [z0, z1]] = b;
  const P = (x: number, y: number, z: number): V3 => [x, y, z];
  return [
    [P(x0, y0, z0), P(x1, y0, z0), P(x1, y1, z0), P(x0, y1, z0)],
    [P(x0, y0, z1), P(x1, y0, z1), P(x1, y1, z1), P(x0, y1, z1)],
    [P(x0, y0, z0), P(x1, y0, z0), P(x1, y0, z1), P(x0, y0, z1)],
    [P(x0, y1, z0), P(x1, y1, z0), P(x1, y1, z1), P(x0, y1, z1)],
    [P(x0, y0, z0), P(x0, y1, z0), P(x0, y1, z1), P(x0, y0, z1)],
    [P(x1, y0, z0), P(x1, y1, z0), P(x1, y1, z1), P(x1, y0, z1)],
  ];
}

/** Keep the part of a convex polyhedron with n·p ≤ c; `cap` is the new face on the plane. */
function cut(faces: Face[], n: V3, c: number): { faces: Face[]; cap: Face } {
  const eps = 1e-9;
  const out: Face[] = [];
  const onPlane: V3[] = [];
  for (const f of faces) {
    const g: V3[] = [];
    for (let i = 0; i < f.length; i++) {
      const p = f[i];
      const q = f[(i + 1) % f.length];
      const fp = dot(n, p) - c;
      const fq = dot(n, q) - c;
      if (fp <= eps) g.push(p);
      if (Math.abs(fp) <= eps) onPlane.push(p);
      if ((fp < -eps && fq > eps) || (fp > eps && fq < -eps)) {
        const t = fp / (fp - fq);
        const m: V3 = [p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1]), p[2] + t * (q[2] - p[2])];
        g.push(m);
        onPlane.push(m);
      }
    }
    if (g.length >= 3) out.push(g);
  }
  // the cap: the points on the plane, in order around their centre
  const pts: V3[] = [];
  for (const p of onPlane) if (!pts.some((q) => Math.hypot(...sub(p, q)) < 1e-7)) pts.push(p);
  let cap: Face = [];
  if (pts.length >= 3) {
    const ctr: V3 = [0, 1, 2].map((k) => pts.reduce((s, p) => s + p[k], 0) / pts.length) as V3;
    const nn = norm(n);
    const u = norm(Math.abs(nn[0]) < 0.9 ? cross(nn, [1, 0, 0]) : cross(nn, [0, 1, 0]));
    const v = cross(nn, u);
    cap = pts
      .map((p) => ({ p, a: Math.atan2(dot(sub(p, ctr), v), dot(sub(p, ctr), u)) }))
      .sort((a, b) => a.a - b.a)
      .map((x) => x.p);
    out.push(cap);
  }
  return { faces: out, cap };
}

const coeffs = (m: LiaModel, i: number): [V3, number] => [m.axes.map((v) => m.items[i].a.get(v) ?? 0) as V3, m.items[i].c];

/** The green solid: the box cut by every drawn constraint. */
function region(m: LiaModel, frame: Frame): Face[] {
  let faces = boxFaces(m.box);
  for (const i of frame.drawn) {
    const [n, c] = coeffs(m, i);
    if (n.every((k) => k === 0)) {
      if (c < 0) return [];
      continue;
    }
    faces = cut(faces, n, c).faces;
    if (!faces.length) return [];
  }
  return faces;
}

// ---------------------------------------------------------------- scene

function clear(g: THREE.Object3D) {
  for (const ch of [...g.children]) {
    clear(ch);
    g.remove(ch);
    const any = ch as THREE.Mesh;
    any.geometry?.dispose();
    const mat = any.material as THREE.Material | THREE.Material[] | undefined;
    (Array.isArray(mat) ? mat : mat ? [mat] : []).forEach((x) => {
      (x as THREE.SpriteMaterial).map?.dispose();
      x.dispose();
    });
  }
}

function solid(faces: Face[], color: number, opacity: number): THREE.Mesh {
  const pos: number[] = [];
  for (const f of faces) for (let i = 1; i + 1 < f.length; i++) pos.push(...f[0], ...f[i], ...f[i + 1]);
  const geo = new THREE.BufferGeometry();
  geo.setAttribute("position", new THREE.Float32BufferAttribute(pos, 3));
  geo.computeVertexNormals();
  const mat = new THREE.MeshLambertMaterial({ color, transparent: true, opacity, side: THREE.DoubleSide, depthWrite: false });
  return new THREE.Mesh(geo, mat);
}

function loop(face: Face, color: number, width = 1): THREE.LineLoop {
  const geo = new THREE.BufferGeometry().setFromPoints(face.map((p) => new THREE.Vector3(...p)));
  return new THREE.LineLoop(geo, new THREE.LineBasicMaterial({ color, linewidth: width }));
}

function label(text: string, color: string, size: number): THREE.Sprite {
  const cv = document.createElement("canvas");
  const g = cv.getContext("2d")!;
  const px = 44;
  g.font = `600 ${px}px system-ui, sans-serif`;
  cv.width = Math.ceil(g.measureText(text).width) + 16;
  cv.height = px + 16;
  g.font = `600 ${px}px system-ui, sans-serif`;
  g.fillStyle = color;
  g.textBaseline = "middle";
  g.fillText(text, 8, cv.height / 2);
  const tex = new THREE.CanvasTexture(cv);
  tex.colorSpace = THREE.SRGBColorSpace;
  const sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, depthTest: false, transparent: true }));
  sp.scale.set((size * cv.width) / cv.height, size, 1);
  return sp;
}

function draw(root: THREE.Group, m: LiaModel, frame: Frame) {
  clear(root);
  const b = m.box;
  const span = Math.max(...b.map(([lo, hi]) => hi - lo));
  const centre = b.map(([lo, hi]) => (lo + hi) / 2);
  root.scale.setScalar(2 / span);
  root.position.set(...(centre.map((c) => (-c * 2) / span) as V3));
  const last = frame.final !== undefined;

  // the box and its axes
  const [[x0, x1], [y0, y1], [z0, z1]] = b;
  const edges = new THREE.LineSegments(
    new THREE.EdgesGeometry(new THREE.BoxGeometry(x1 - x0, y1 - y0, z1 - z0)),
    new THREE.LineBasicMaterial({ color: COLOR.box }),
  );
  edges.position.set(...(centre as V3));
  root.add(edges);
  const ls = span * 0.085;
  const axisEnd: V3[] = [
    [x1, y0, z0],
    [x0, y1, z0],
    [x0, y0, z1],
  ];
  axisEnd.forEach((e, k) => {
    const name = label(`${m.axes[k]} ${num(b[k][1])}`, COLOR.ink, ls);
    const away: V3 = [...e];
    away[k] += span * 0.06;
    name.position.set(...away);
    root.add(name);
  });
  const origin = label(`${num(x0)}, ${num(y0)}, ${num(z0)}`, "#6b7280", ls * 0.8);
  origin.position.set(x0 - span * 0.04, y0 - span * 0.04, z0 - span * 0.04);
  root.add(origin);

  // what is still allowed (green), and what each constraint rules out (red)
  const green = region(m, frame);
  if (green.length) {
    root.add(solid(green, COLOR.space, frame.drawn.length ? 0.55 : 0.18));
    if (frame.drawn.length) for (const f of green) root.add(loop(f, 0x1b6b30));
  }
  for (const i of frame.drawn) {
    const [n, c] = coeffs(m, i);
    if (n.every((k) => k === 0)) continue;
    const out = cut(boxFaces(b), [-n[0], -n[1], -n[2]], -c).faces;
    if (out.length) root.add(solid(out, COLOR.out, i === frame.fresh ? 0.2 : 0.1));
    // the plane itself, inside the box
    const sec = cut(boxFaces(b), n, c).cap;
    if (sec.length >= 3) {
      const it = m.items[i];
      const col = last && frame.final === "unsat" && m.conflictIds.has(i) ? COLOR.blame : i === frame.fresh ? COLOR.fresh : it.derived ? COLOR.derived : COLOR.line;
      root.add(loop(sec, col, 2));
      // the label sits between the centre and a corner, so labels of planes through the centre do not overlap
      const ctr = [0, 1, 2].map((k) => sec.reduce((s, p) => s + p[k], 0) / sec.length) as V3;
      const corner = sec[(i * 2) % sec.length];
      const tag = label(it.text, "#" + col.toString(16).padStart(6, "0"), ls * 0.8);
      tag.position.set(...(ctr.map((v, k) => v + (corner[k] - v) * 0.55) as V3));
      root.add(tag);
    }
  }

  // integer solutions at the end of a satisfiable check
  if (frame.final === "sat" && span <= 14 && green.length) {
    const inside = (p: V3) => frame.drawn.every((i) => {
      const [n, c] = coeffs(m, i);
      return dot(n, p) <= c + 1e-9;
    });
    const dots: V3[] = [];
    for (let x = Math.ceil(x0); x <= x1; x++) for (let y = Math.ceil(y0); y <= y1; y++) for (let z = Math.ceil(z0); z <= z1; z++) if (inside([x, y, z])) dots.push([x, y, z]);
    const geo = new THREE.SphereGeometry(span * 0.012, 8, 6);
    const mat = new THREE.MeshLambertMaterial({ color: 0x1b6b30 });
    const inst = new THREE.InstancedMesh(geo, mat, Math.min(dots.length, 3000));
    const mx = new THREE.Matrix4();
    dots.slice(0, 3000).forEach((p, k) => inst.setMatrixAt(k, mx.makeTranslation(...p)));
    root.add(inst);
  }

  // Simplex's candidate point and its path
  if (frame.path && frame.path.length > 1) {
    const geo = new THREE.BufferGeometry().setFromPoints(frame.path.map((p) => new THREE.Vector3(...(p as V3))));
    root.add(new THREE.Line(geo, new THREE.LineBasicMaterial({ color: COLOR.point })));
    for (const p of frame.path.slice(0, -1)) {
      const s = new THREE.Mesh(new THREE.SphereGeometry(span * 0.012, 10, 8), new THREE.MeshLambertMaterial({ color: COLOR.point }));
      s.position.set(...(p as V3));
      root.add(s);
    }
  }
  if (frame.point) {
    const p = frame.point as V3;
    const s = new THREE.Mesh(new THREE.SphereGeometry(span * 0.022, 16, 12), new THREE.MeshLambertMaterial({ color: COLOR.point }));
    s.position.set(...p);
    root.add(s);
    const t = label(`(${p.map(num).join(", ")})`, "#b35c00", ls);
    t.position.set(p[0], p[1], p[2] + span * 0.06);
    root.add(t);
  }
}
