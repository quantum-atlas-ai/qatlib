import {LayeredNebula} from "./dependency-layers.js";

// Canvas layout for library groups, theorem stars and their dependency paths.
const TAU = Math.PI * 2;
const DUST = ["#38dcd7", "#637ef5", "#ef75d8"];
const DEFAULT_ORBIT = {yaw: -.35, pitch: .30};
// Band order matches the three library layers. Positions use the same
// aspect ratio for group stars, declaration stars, edges and the fog.
const BANDS = [[12, 140], [180, 277], [352, 489]];
const ASPECT = .82;
const MIST_SIZE = 1090;

function random(seed) {
  return () => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed / 4294967296;
  };
}

function radialPoint(radius, angle) {
  return {x: radius * Math.cos(angle), y: radius * Math.sin(angle) * ASPECT};
}

function polar(point) {
  const y = point.y / ASPECT;
  return {radius: Math.hypot(point.x, y), angle: Math.atan2(y, point.x)};
}

function bandPoint(layer, progress, angle) {
  const [inner, outer] = BANDS[layer];
  return radialPoint(inner + (outer - inner) * progress, angle);
}

function swirl(layer, rng, scatter) {
  const radial = Math.sqrt(rng());
  const arm = Math.floor(rng() * 3) * TAU / 3;
  const angle = arm + radial * 2.25 + layer * .91 + (rng() - .5) * scatter;
  return bandPoint(layer, radial, angle);
}

const phase = layer => .36 + layer * TAU / 3;

function makeSprite(color, halo) {
  const sprite = document.createElement("canvas");
  sprite.width = sprite.height = 48;
  const ctx = sprite.getContext("2d");
  const gradient = ctx.createRadialGradient(24, 24, 0, 24, 24, 24);
  gradient.addColorStop(0, "#fff");
  gradient.addColorStop(.13, color);
  gradient.addColorStop(.35, color + halo);
  gradient.addColorStop(1, color + "00");
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, 48, 48);
  return sprite;
}

function texture(radial = false) {
  const canvas = document.createElement("canvas");
  canvas.width = radial ? 560 : 680;
  canvas.height = 440;
  const ctx = canvas.getContext("2d");
  const pixels = ctx.createImageData(canvas.width, canvas.height);
  const rng = random(23419081);
  const field = Float32Array.from({length: 4096}, rng);
  const smooth = v => v * v * (3 - 2 * v);
  function noise(x, y) {
    const ix = Math.floor(x);
    const iy = Math.floor(y);
    const a = smooth(x - ix);
    const b = smooth(y - iy);
    const index = (ix * 157 + iy * 277) & 4095;
    const top = field[index] * (1 - a) + field[(index + 157) & 4095] * a;
    const bottom = field[(index + 277) & 4095] * (1 - a) + field[(index + 434) & 4095] * a;
    return top * (1 - b) + bottom * b;
  }
  function fbm(x, y) {
    return noise(x, y) * .54 + noise(x * 2.1 + 11, y * 2.1 - 9) * .28
      + noise(x * 4.4, y * 4.4 + 7) * .13 + noise(x * 9.2, y * 9.2) * .05;
  }
  const tint = [[29, 164, 151], [61, 92, 230], [160, 46, 157]];
  const radialTint = [[48, 206, 189], [94, 115, 249], [236, 103, 198]];
  for (let y = 0; y < canvas.height; y++) {
    for (let x = 0; x < canvas.width; x++) {
      const at = (y * canvas.width + x) * 4;
      if (radial) {
        const u = x / canvas.width - .5;
        const v = y / canvas.height - .5;
        const r = Math.hypot(u, v) * MIST_SIZE;
        const phase = Math.atan2(v, u) - r * .017;
        const drift = (fbm(u * 9 + 12, v * 9 + 15) - .5) * 1.5;
        const structure = Math.max(0, fbm(u * 24 + drift, v * 24 - drift) - .18) ** 1.7;
        let light = 0;
        let red = 0;
        let green = 0;
        let blue = 0;
        for (const [layer, [inner, outer]] of BANDS.entries()) {
          const center = (inner + outer) / 2;
          const width = (outer - inner) * .43;
          const wave = .32 + .68 * (.5 + .5 * Math.cos(3 * (phase + drift + layer))) ** 1.6;
          const plume = structure * wave * Math.exp(-.5 * ((r - center) / width) ** 2);
          const [cr, cg, cb] = radialTint[layer];
          light += plume;
          red += cr * plume;
          green += cg * plume;
          blue += cb * plume;
        }
        if (light > .001) {
          pixels.data[at] = red / light;
          pixels.data[at + 1] = green / light;
          pixels.data[at + 2] = blue / light;
          pixels.data[at + 3] = Math.min(126, light * 244);
        }
        continue;
      }
      const u = (x / canvas.width - .56) * 3.2;
      const v = (y / canvas.height - .48) * 2.85;
      const warp = fbm(u * 2.8 + 14, v * 2.8 - 4) - .5;
      const radius = Math.hypot(u, v);
      const angle = Math.atan2(v, u) - radius * 2.7 + warp * 1.6;
      const detail = fbm(u * 6.7 + warp * 7.5, v * 6.7 + warp * 4.4);
      const haze = Math.pow(Math.max(0, detail - .22), 2) * Math.exp(-.53 * radius * radius);
      for (let k = 0; k < 3; k++) {
        let channel = [4, 7, 16][k] + haze * [16, 23, 54][k];
        for (let layer = 0; layer < 3; layer++) {
          const turn = 1 - Math.cos(angle - phase(layer));
          const plume = Math.exp(-turn * 5.5) * haze;
          const filament = Math.exp(-turn * 20) * Math.max(0, detail - .38) ** 2;
          channel += tint[layer][k] * (plume * .92 + filament * .37);
        }
        pixels.data[at + k] = channel;
      }
      pixels.data[at + 3] = 255;
    }
  }
  ctx.putImageData(pixels, 0, 0);
  return canvas;
}

export class DependencyNebula {
  constructor(canvas, model, handlers, colors) {
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d", {alpha: false});
    this.model = model;
    this.handlers = handlers;
    this.colors = colors;
    this.mode = "2d";
    this.unit = 1;
    this.width = canvas.clientWidth;
    this.height = canvas.clientHeight;
    this.camera = {x: 0, y: 0, zoom: 1, ...DEFAULT_ORBIT};
    this.goal = {...this.camera};
    this.targets = [];
    this.reducedMotion = matchMedia("(prefers-reduced-motion: reduce)");
    this.texture = texture();
    this.mist = texture(true);
    this.sprites = colors.map(color => makeSprite(color, "3a"));
    this.groupStars = [];
    this.related = [];
    this.dust = [];
    this.backdrop = [];
    this.pointers = new Map();
    const rng = random(713);
    this.model.groups.forEach(([layer], id) => {
      const point = swirl(layer, rng, 1.5);
      const members = this.model.members[id].length;
      const radius = Math.min(2.65, 1.1 + Math.log1p(members) * .22);
      this.groupStars[id] = {id, ...point, layer, radius, kind: "group"};
    });
    const groupEdges = new Map();
    this.model.nodes.forEach(([, , dependencies], id) => {
      const from = this.model.groupOf(id);
      for (const dependency of dependencies) {
        const to = this.model.groupOf(dependency);
        if (from === to) continue;
        const key = from * this.groupStars.length + to;
        groupEdges.set(key, (groupEdges.get(key) ?? 0) + 1);
      }
    });
    this.overviewEdges = [];
    const shown = new Uint16Array(this.groupStars.length);
    for (const [key] of [...groupEdges].sort((a, b) => b[1] - a[1])) {
      const from = this.groupStars[Math.floor(key / this.groupStars.length)];
      const to = this.groupStars[key % this.groupStars.length];
      const distance = Math.hypot(from.x - to.x, from.y - to.y);
      if (distance < 28 || distance > 410 || shown[from.id] >= 13 || shown[to.id] >= 13) continue;
      shown[from.id]++;
      shown[to.id]++;
      this.overviewEdges.push([from, to]);
      if (this.overviewEdges.length === 124) break;
    }
    for (let i = 0; i < 7800; i++) {
      const layer = i % this.colors.length;
      this.dust.push({layer, ...swirl(layer, rng, 2.28),
        radius: .16 + rng() ** 4 * .87, alpha: .11 + rng() * .36});
    }
    for (let i = 0; i < 950; i++) {
      this.backdrop.push({x: rng(), y: rng(), radius: .22 + rng() ** 7 * 1.23, alpha: .07 + rng() * .48});
    }
    new ResizeObserver(() => this.invalidate()).observe(canvas);
    this.bind();
    this.invalidate();
  }

  setSelection(group, theorem, up = [], down = []) {
    const groupChanged = this.group !== group;
    const changed = groupChanged || this.theorem !== theorem;
    this.group = group;
    this.theorem = theorem;
    this.up = up;
    this.down = down;
    if (groupChanged) this.related = [];
    if (groupChanged && group !== undefined) {
      const counts = new Map();
      for (const id of this.model.members[group]) {
        for (const adjacent of [this.model.nodes[id][2], this.model.reverse[id]]) {
          for (const node of adjacent) {
            const target = this.model.groupOf(node);
            if (target !== group) counts.set(target, (counts.get(target) ?? 0) + 1);
          }
        }
      }
      this.related = [...counts].sort((a, b) => b[1] - a[1]).slice(0, 34).map(([id]) => id);
    }
    if (changed) {
      this.hover = undefined;
      this.fit(false);
    } else this.invalidate();
  }

  setView(mode) {
    if (mode === this.mode) return;
    this.mode = mode;
    if (mode === "3d") this.layers ??= new LayeredNebula(this, random(53127), this.colors);
    this.hover = undefined;
    this.handlers.onHover();
    this.fit();
    this.camera = {...this.goal};
  }

  fit(resetOrbit = true) {
    const group = this.theorem === undefined ? this.group : this.model.groupOf(this.theorem);
    const point = this.groupStars[group];
    if (this.mode === "3d") {
      const star = this.layers.stars[group];
      const orbit = resetOrbit ? DEFAULT_ORBIT : {yaw: this.goal.yaw, pitch: this.goal.pitch};
      this.goal = {...orbit, x: (star?.x ?? 0) * .54, y: (star?.z ?? 0) * .54,
        zoom: group === undefined ? 1 : 1.08};
    } else {
      const zoom = this.theorem !== undefined ? 1.12 : group !== undefined ? 1.48 : 1;
      this.goal = {...DEFAULT_ORBIT, x: point?.x ?? 0, y: point?.y ?? 0, zoom};
    }
    this.invalidate();
  }

  orbit(dx, dy) {
    this.goal.yaw += dx * .008;
    this.goal.pitch = Math.min(.54, Math.max(.15, this.goal.pitch + dy * .0045));
    this.invalidate();
  }

  zoom(multiplier, anchor) {
    if (!(this.unit > 0) || !Number.isFinite(multiplier)) return;
    const previous = this.goal.zoom;
    this.goal.zoom = Math.min(8, Math.max(.43, previous * multiplier));
    if (anchor && this.mode === "2d") {
      const [x, y] = this.origin();
      const delta = (1 / previous - 1 / this.goal.zoom) / this.unit;
      this.goal.x += (anchor.x - x) * delta;
      this.goal.y += (anchor.y - y) * delta;
    }
    this.invalidate();
  }

  origin() {
    const compact = this.width < 800;
    const browse = this.handlers.isSidebarOpen();
    const inspect = this.handlers.isDetailOpen();
    const x = this.width * .5 + (!compact ? (browse ? 120 : 0) - (inspect ? 112 : 0) : 0);
    return [x, this.height * (compact && inspect ? .38 : .49)];
  }

  invalidate() {
    if (this.frame !== undefined) return;
    this.frame = requestAnimationFrame(() => {
      this.frame = undefined;
      this.draw();
    });
  }

  screen(point) {
    const [x, y] = this.origin();
    const zoom = this.unit * this.camera.zoom;
    return {x: x + (point.x - this.camera.x) * zoom, y: y + (point.y - this.camera.y) * zoom};
  }

  draw() {
    const {ctx, canvas} = this;
    this.width = canvas.clientWidth;
    this.height = canvas.clientHeight;
    if (!this.width || !this.height) return;
    const compact = this.width < 800;
    this.unit = this.mode === "3d"
      ? Math.min(this.width / (compact ? 825 : 1160), this.height / 910)
      : Math.min(this.width / (compact ? 1070 : 1240), this.height / 925);
    const resolution = Math.min(devicePixelRatio, 2);
    const w = Math.round(this.width * resolution);
    const h = Math.round(this.height * resolution);
    if (canvas.width !== w || canvas.height !== h) {
      canvas.width = w;
      canvas.height = h;
    }
    ctx.setTransform(resolution, 0, 0, resolution, 0, 0);
    let moving = false;
    for (const key of ["x", "y", "zoom", "yaw", "pitch"]) {
      const delta = this.goal[key] - this.camera[key];
      const threshold = key === "x" || key === "y" ? .15 : .002;
      if (Math.abs(delta) > threshold && !this.reducedMotion.matches) {
        this.camera[key] += delta * .19;
        moving = true;
      } else this.camera[key] = this.goal[key];
    }

    ctx.drawImage(this.texture, 0, 0, this.width, this.height);
    for (const p of this.backdrop) {
      ctx.fillStyle = `rgba(202,218,255,${p.alpha})`;
      ctx.fillRect(p.x * this.width, p.y * this.height, p.radius, p.radius);
    }
    this.targets = [];
    if (this.mode === "3d") {
      this.layers.draw();
    } else {
      const dim = this.theorem !== undefined ? .35 : this.group !== undefined ? .64 : 1;
      this.drawBands(dim);
      this.drawDust(dim);
      if (this.theorem === undefined) this.drawGroups();
      else this.drawNeighborhood();
      if (this.group === undefined && this.theorem === undefined) this.labelBands();
    }
    if (moving) this.invalidate();
  }

  drawBands(dim) {
    const {ctx} = this;
    const center = this.screen({x: 0, y: 0});
    const scale = this.unit * this.camera.zoom;
    const width = MIST_SIZE * scale;
    const height = width * ASPECT;
    ctx.globalAlpha = dim;
    ctx.drawImage(this.mist, center.x - width / 2, center.y - height / 2, width, height);
    for (const [layer, radius] of [157, 313, 503].entries()) {
      ctx.beginPath();
      ctx.ellipse(center.x, center.y, radius * scale, radius * scale * ASPECT, 0, 0, TAU);
      ctx.strokeStyle = this.colors[layer];
      ctx.lineWidth = .8;
      ctx.globalAlpha = .17 * dim;
      ctx.stroke();
    }
    ctx.globalAlpha = 1;
  }

  labelBands() {
    this.model.layerNames.forEach((label, layer) => {
      const angle = this.width < 800 ? -.95 : -.65;
      const point = this.screen(bandPoint(layer, [.51, .34, .36][layer], angle));
      this.label({...point, layer}, label, 0, true);
    });
  }

  drawDust(dim) {
    const {ctx} = this;
    const [ox, oy] = this.origin();
    const scale = this.unit * this.camera.zoom;
    const dx = ox - this.camera.x * scale;
    const dy = oy - this.camera.y * scale;
    for (const p of this.dust) {
      const x = dx + p.x * scale;
      const y = dy + p.y * scale;
      if (x < 0 || y < 0 || x > this.width || y > this.height) continue;
      ctx.globalAlpha = p.alpha * dim;
      ctx.fillStyle = DUST[p.layer];
      const r = Math.min(2.2, p.radius * scale);
      ctx.fillRect(x, y, r + .35, r + .35);
    }
    ctx.globalAlpha = 1;
  }

  glow(point, size, alpha = 1) {
    const {ctx} = this;
    ctx.globalAlpha = alpha;
    ctx.drawImage(this.sprites[point.layer], point.x - size, point.y - size, size * 2, size * 2);
    ctx.globalAlpha = 1;
  }

  drawGroups() {
    const focus = this.groupStars[this.group];
    const related = new Set(this.related);
    if (!focus) {
      for (const [from, to] of this.overviewEdges) {
        this.curve(this.screen(from), this.screen(to), this.colors[from.layer], .14);
      }
    }
    if (focus) {
      for (const target of this.related) {
        this.curve(this.screen(focus), this.screen(this.groupStars[target]), this.colors[focus.layer], .29);
      }
    }
    for (const star of this.groupStars) {
      const on = {...star, ...this.screen(star)};
      if (on.x < -36 || on.y < -36 || on.x > this.width + 36 || on.y > this.height + 36) continue;
      const fade = !focus || related.has(star.id) ? 1 : .33;
      const size = Math.min(19, (5.2 + star.radius * 3.1) * Math.sqrt(this.unit * this.camera.zoom));
      this.glow(on, size, fade * .88);
      this.targets.push({...on, hit: 8});
    }
    if (focus) {
      const on = {...focus, ...this.screen(focus)};
      this.glow(on, 63, .74);
      this.ring(on, 14);
      const members = this.model.members[focus.id];
      const center = polar(focus);
      const [inner, outer] = BANDS[focus.layer];
      const highlights = new Map(members.map((id, i) => {
        const angle = i * 2.3999632 + focus.id;
        const spread = Math.sqrt((i + 1) / members.length);
        const radial = Math.sin(angle);
        const available = radial > 0 ? outer - center.radius : center.radius - inner;
        const radius = center.radius + Math.min(73, available) * spread * radial;
        const theta = center.angle + Math.cos(angle) * spread * Math.min(1.06, 113 / center.radius);
        const star = this.screen(radialPoint(radius, theta));
        return [id, {...star, kind: "theorem", id, layer: focus.layer}];
      }));
      let segments = 0;
      for (const [id, from] of highlights) {
        if (segments >= 96) break;
        for (const dependency of this.model.nodes[id][2]) {
          const to = highlights.get(dependency);
          if (to && segments < 96) {
            this.curve(from, to, this.colors[focus.layer], .22);
            segments++;
          }
        }
      }
      for (const node of highlights.values()) {
        this.glow(node, members.length > 140 ? 8 : 15, 1);
        this.targets.push({...node, hit: 7});
      }
      this.label(on, this.model.titleOf(focus.id), 25, true);
    }
    if (this.hover && this.theorem === undefined) {
      const star = this.targets.find(p => p.id === this.hover.id && p.kind === this.hover.kind);
      if (star) this.ring(star, 9);
    }
  }

  drawNeighborhood() {
    const focusGroup = this.groupStars[this.model.groupOf(this.theorem)];
    const focal = {...this.screen(focusGroup), layer: focusGroup.layer};
    const narrow = this.width < 800;
    const center = polar(focusGroup);
    const hit = Math.min(16, 21 * this.unit * this.camera.zoom);
    // Use a wider arc in the inner bands to leave room for each star.
    for (const [ids, sign] of [[this.up, -1], [this.down, 1]]) {
      const buckets = BANDS.map(() => []);
      for (const id of ids) {
        const layer = this.model.groups[this.model.groupOf(id)][0];
        buckets[layer].push(id);
      }
      buckets.forEach((bucket, layer) => bucket.forEach((id, i) => {
        const start = layer === focusGroup.layer ? .55 : .42;
        const end = [2.72, 1.85, 1.60][layer];
        const fraction = bucket.length === 1 ? .15 : i / (bucket.length - 1);
        const angle = center.angle + sign * (start + (end - start) * fraction);
        const world = bandPoint(layer, i % 2 ? .60 : .95, angle);
        const star = {...this.screen(world), layer, id, kind: "theorem"};
        const [from, to] = sign < 0 ? [star, focal] : [focal, star];
        this.curve(from, to, this.colors[star.layer], .66, true);
        this.glow(star, hit * (this.hover?.id === id ? 1.9 : 1.3), .94);
        if (ids.length <= (narrow ? 1 : 6) || this.hover?.id === id) {
          const labelOffset = star.y < focal.y ? -15 : 15;
          this.label(star, this.model.shortName(id), labelOffset);
        }
        this.targets.push({...star, hit});
      }));
    }
    this.glow(focal, 88, .85);
    this.ring(focal, 18);
    this.ring(focal, 26, .27);
    this.label(focal, this.model.shortName(this.theorem), 30, true);
  }

  curve(from, to, color, alpha, arrow = false) {
    const {ctx} = this;
    const vx = to.x - from.x;
    const vy = to.y - from.y;
    const length = Math.hypot(vx, vy) || 1;
    const bend = Math.min(57, length * .18);
    const ax = -vy / length * bend;
    const ay = vx / length * bend;
    ctx.globalAlpha = alpha * .22;
    ctx.strokeStyle = color;
    ctx.lineWidth = arrow ? 7 : 3;
    ctx.beginPath();
    ctx.moveTo(from.x, from.y);
    ctx.quadraticCurveTo((from.x + to.x) / 2 + ax, (from.y + to.y) / 2 + ay, to.x, to.y);
    ctx.stroke();
    ctx.globalAlpha = alpha;
    ctx.lineWidth = arrow ? 1.3 : .8;
    ctx.stroke();
    if (arrow) {
      const t = .76;
      const x = from.x + vx * t + 2 * (1 - t) * t * ax;
      const y = from.y + vy * t + 2 * (1 - t) * t * ay;
      const angle = Math.atan2(vy + 2 * (1 - 2 * t) * ay, vx + 2 * (1 - 2 * t) * ax);
      ctx.beginPath();
      ctx.moveTo(x + 5 * Math.cos(angle), y + 5 * Math.sin(angle));
      ctx.lineTo(x + 6 * Math.cos(angle + 2.6), y + 6 * Math.sin(angle + 2.6));
      ctx.lineTo(x + 6 * Math.cos(angle - 2.6), y + 6 * Math.sin(angle - 2.6));
      ctx.fillStyle = color;
      ctx.fill();
    }
    ctx.globalAlpha = 1;
  }

  ring(point, radius, alpha = .7) {
    const {ctx} = this;
    ctx.globalAlpha = alpha;
    ctx.strokeStyle = this.colors[point.layer];
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.arc(point.x, point.y, radius, 0, TAU);
    ctx.stroke();
    ctx.globalAlpha = 1;
  }

  label(point, value, offset, emphasized = false) {
    const {ctx} = this;
    const label = value.length > 43 ? value.slice(0, 41) + "…" : value;
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.font = `${emphasized ? 600 : 500} ${emphasized ? 13 : 11}px system-ui, sans-serif`;
    const padding = ctx.measureText(label).width / 2 + 10;
    const left = this.width >= 800 && this.handlers.isSidebarOpen() ? 304 : 0;
    const right = this.width >= 800 && this.handlers.isDetailOpen() ? this.width - 326 : this.width;
    const x = Math.min(right - padding, Math.max(left + padding, point.x));
    ctx.strokeStyle = "#080d1d";
    ctx.lineWidth = 3.8;
    ctx.lineJoin = "round";
    ctx.strokeText(label, x, point.y + offset);
    ctx.fillStyle = this.colors[point.layer];
    ctx.fillText(label, x, point.y + offset);
  }

  hit(x, y) {
    let best;
    let distance = Infinity;
    for (let i = this.targets.length - 1; i >= 0; i--) {
      const star = this.targets[i];
      const delta = (star.x - x) ** 2 + (star.y - y) ** 2;
      if (delta < distance && delta < star.hit ** 2) {
        best = star;
        distance = delta;
      }
    }
    return best;
  }

  bind() {
    const {canvas, pointers} = this;
    let drag;
    const position = event => {
      const rect = canvas.getBoundingClientRect();
      return {x: event.clientX - rect.left, y: event.clientY - rect.top};
    };
    canvas.addEventListener("keydown", event => {
      if (this.mode !== "3d") return;
      const arrows = {ArrowLeft: [-26, 0], ArrowRight: [26, 0], ArrowUp: [0, -16], ArrowDown: [0, 16]};
      if (!Object.hasOwn(arrows, event.key)) return;
      event.preventDefault();
      this.orbit(...arrows[event.key]);
    });
    canvas.addEventListener("wheel", event => {
      event.preventDefault();
      this.zoom(Math.exp(-event.deltaY * .0016), position(event));
    }, {passive: false});
    canvas.addEventListener("pointerdown", event => {
      if (event.button !== 0) return;
      const point = position(event);
      pointers.set(event.pointerId, point);
      canvas.setPointerCapture(event.pointerId);
      if (pointers.size === 1) drag = {...point, start: point, moved: false};
      else if (drag) drag.moved = true;
      this.handlers.onHover();
    });
    canvas.addEventListener("pointermove", event => {
      const point = position(event);
      if (pointers.has(event.pointerId)) {
        const previous = pointers.get(event.pointerId);
        pointers.set(event.pointerId, point);
        if (pointers.size > 1) {
          const other = [...pointers].find(([id]) => id !== event.pointerId)[1];
          const before = Math.hypot(previous.x - other.x, previous.y - other.y);
          const after = Math.hypot(point.x - other.x, point.y - other.y);
          if (before > 8) this.zoom(after / before, {x: (point.x + other.x) / 2, y: (point.y + other.y) / 2});
        } else if (drag) {
          drag.moved ||= Math.hypot(point.x - drag.start.x, point.y - drag.start.y) > 4;
          if (!drag.moved) return;
          const dx = point.x - previous.x;
          const dy = point.y - previous.y;
          if (this.mode === "3d" && !event.shiftKey) {
            this.orbit(dx, dy);
          } else {
            const scale = this.unit * this.goal.zoom;
            if (!(scale > 0)) return;
            this.goal.x -= dx / scale;
            this.goal.y -= dy / scale;
            this.invalidate();
          }
        }
        canvas.dataset.dragging = "true";
        return;
      }
      const hit = this.hit(point.x, point.y);
      const changed = hit?.id !== this.hover?.id || hit?.kind !== this.hover?.kind;
      this.hover = hit;
      canvas.dataset.pointing = String(Boolean(hit));
      this.handlers.onHover(hit, point);
      if (changed) this.invalidate();
    });
    canvas.addEventListener("pointerleave", () => {
      this.hover = undefined;
      this.handlers.onHover();
      this.invalidate();
    });
    canvas.addEventListener("pointerup", event => {
      pointers.delete(event.pointerId);
      if (!pointers.size && !drag?.moved) {
        const {x, y} = position(event);
        const hit = this.hit(x, y);
        if (hit) this.handlers.onSelect(hit);
      }
      if (!pointers.size) drag = undefined;
      delete canvas.dataset.dragging;
    });
    canvas.addEventListener("pointercancel", event => {
      pointers.delete(event.pointerId);
      drag = undefined;
      delete canvas.dataset.dragging;
    });
  }
}
