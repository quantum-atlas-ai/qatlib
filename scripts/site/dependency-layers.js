// A perspective view of the same graph. Layer indices map directly to altitude.
const TAU = 2 * Math.PI;
const GOLDEN_ANGLE = 2.399963229728653;
const SPACING = 218;
const RADIUS = 360;

function tierPoint(x, z, layer) {
  return {x, z, height: (layer - 1) * SPACING, layer};
}

function orbitPoint(angle, distance, layer) {
  return tierPoint(Math.cos(angle) * distance, Math.sin(angle) * distance, layer);
}

export class LayeredNebula {
  constructor(host, rng, colors) {
    this.host = host;
    this.colors = colors;
    this.stars = host.groupStars.map(star => {
      const r = 17 + Math.sqrt(rng()) * 317;
      const arm = Math.floor(rng() * 3) * TAU / 3;
      const angle = arm + r / 150 + (rng() - .5) * 1.12 + star.layer * .48;
      return {...star, ...orbitPoint(angle, r, star.layer)};
    });
    this.dust = Array.from({length: 2850}, (_, i) => {
      const layer = i % colors.length;
      const r = Math.sqrt(rng()) * (RADIUS - 3);
      const angle = Math.floor(rng() * 3) * TAU / 3 + r / 150 + (rng() - .5) * 1.65 + layer * .48;
      return {...orbitPoint(angle, r, layer), size: .25 + rng() ** 4 * 1.08, opacity: .14 + rng() * .44};
    });
  }

  project(point) {
    const view = this.view;
    const x = point.x - view.x;
    const z = point.z - view.z;
    const right = x * view.cy + z * view.sy;
    const forward = -x * view.sy + z * view.cy;
    const height = point.height * view.cp - forward * view.sp;
    const depth = forward * view.cp + point.height * view.sp;
    const perspective = 1260 / Math.max(420, 1260 - depth);
    return {x: view.ox + right * view.scale * perspective,
      y: view.oy - height * view.scale * perspective,
      perspective, depth};
  }

  draw() {
    const {host} = this;
    const [ox, oy] = host.origin();
    const {x, y, zoom, yaw, pitch} = host.camera;
    this.view = {ox, oy, x, z: y, scale: host.unit * zoom,
      cy: Math.cos(yaw), sy: Math.sin(yaw), cp: Math.cos(pitch), sp: Math.sin(pitch)};
    this.drawPlanes();
    this.drawDust();
    if (host.theorem === undefined) this.drawGroups();
    else this.drawNeighborhood();
  }

  ringPath(radius, layer) {
    const {ctx} = this.host;
    for (let i = 0; i <= 90; i++) {
      const {x, y} = this.project(orbitPoint(TAU * i / 90, radius, layer));
      if (i === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    }
    ctx.closePath();
  }

  drawPlanes() {
    const {host, colors} = this;
    const {ctx} = host;
    // The rails share the same orientation and spacing as the plotted planes.
    ctx.strokeStyle = "#7598e8";
    ctx.lineWidth = .75;
    ctx.globalAlpha = .24;
    ctx.setLineDash([3, 7]);
    for (const angle of [Math.PI * .46, Math.PI * 1.53]) {
      const a = this.project(orbitPoint(angle, RADIUS, 0));
      const b = this.project(orbitPoint(angle, RADIUS, 2));
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.stroke();
    }
    ctx.setLineDash([]);
    ctx.globalAlpha = 1;

    for (const layer of [0, 1, 2]) {
      const center = this.project(tierPoint(0, 0, layer));
      const glow = ctx.createRadialGradient(center.x, center.y, 0, center.x, center.y,
        Math.max(1, RADIUS * this.view.scale * center.perspective * .88));
      glow.addColorStop(0, colors[layer] + "35");
      glow.addColorStop(.72, colors[layer] + "0d");
      glow.addColorStop(1, colors[layer] + "04");
      ctx.beginPath();
      this.ringPath(RADIUS, layer);
      ctx.fillStyle = glow;
      ctx.fill();

      // Each ellipse and radial guide is a circle or straight line in world space.
      ctx.strokeStyle = colors[layer];
      ctx.lineWidth = 1;
      ctx.globalAlpha = .36;
      ctx.stroke();
      ctx.globalAlpha = .15;
      ctx.lineWidth = .85;
      for (const radius of [84, 166, 251, 315]) {
        ctx.beginPath();
        this.ringPath(radius, layer);
        ctx.stroke();
      }
      ctx.globalAlpha = .095;
      for (let i = 0; i < 12; i++) {
        const edge = this.project(orbitPoint(i * TAU / 12, RADIUS, layer));
        ctx.beginPath();
        ctx.moveTo(center.x, center.y);
        ctx.lineTo(edge.x, edge.y);
        ctx.stroke();
      }
      ctx.globalAlpha = 1;
    }
  }

  drawDust() {
    const {host, colors} = this;
    const {ctx} = host;
    const dim = host.theorem !== undefined ? .48 : .87;
    for (const grain of this.dust) {
      const p = this.project(grain);
      if (!this.visible(p)) continue;
      ctx.globalAlpha = grain.opacity * dim;
      ctx.fillStyle = colors[grain.layer];
      const size = grain.size * p.perspective * this.view.scale;
      ctx.fillRect(p.x, p.y, size, size);
    }
    ctx.globalAlpha = 1;
  }

  visible(point, margin = 26) {
    const {width, height} = this.host;
    return point.x >= -margin && point.x <= width + margin
      && point.y >= -margin && point.y <= height + margin;
  }

  drawGroups() {
    const {host, colors} = this;
    const focus = this.stars[host.group];
    const related = new Set(host.related);
    const stars = this.stars.map(star => ({...star, ...this.project(star)}));
    const projectedFocus = stars[host.group];
    if (focus) {
      for (const target of host.related) {
        host.curve(projectedFocus, stars[target], colors[focus.layer], .31);
      }
    } else {
      for (const [from, to] of host.overviewEdges) {
        host.curve(stars[from.id], stars[to.id], colors[from.layer], .11);
      }
    }
    for (const star of [...stars].sort((a, b) => a.depth - b.depth)) {
      if (!this.visible(star)) continue;
      const size = (4.5 + star.radius * 2.8) * Math.sqrt(star.perspective * this.view.scale);
      host.glow(star, Math.min(19, size), focus && !related.has(star.id) ? .28 : .91);
      if (host.hover?.kind === star.kind && host.hover.id === star.id) host.ring(star, 8);
      host.targets.push({...star, hit: Math.max(6, size * .65)});
    }
    if (focus) this.drawMembers(focus, projectedFocus);
    this.labelLayers();
  }

  labelLayers() {
    const {host} = this;
    // Compensate for yaw so the label remains on the left front edge of each plane.
    const angle = Math.PI * .92 + host.camera.yaw;
    for (const layer of [2, 1, 0]) {
      const anchor = this.project(orbitPoint(angle, RADIUS * 1.04, layer));
      if (anchor.y >= 65 && anchor.y <= host.height - 32) {
        host.label({...anchor, layer}, host.model.layerNames[layer], -8, true);
      }
    }
  }

  drawMembers(focus, projectedFocus) {
    const {host, colors} = this;
    const ids = host.model.members[focus.id];
    const members = new Map(ids.map((id, i) => {
      const angle = focus.id + i * GOLDEN_ANGLE;
      const distance = 12 + 96 * Math.sqrt((i + 1) / ids.length);
      const x = focus.x + Math.cos(angle) * distance;
      const z = focus.z + Math.sin(angle) * distance;
      const p = this.project(tierPoint(x, z, focus.layer));
      return [id, {...p, layer: focus.layer, id, kind: "theorem"}];
    }));
    let arcs = 0;
    for (const [id, from] of members) {
      if (arcs >= 92) break;
      for (const dependency of host.model.nodes[id][2]) {
        const to = members.get(dependency);
        if (to && arcs < 92) {
          host.curve(from, to, colors[focus.layer], .24);
          arcs++;
        }
      }
    }
    host.glow(projectedFocus, 45, .72);
    host.ring(projectedFocus, 11);
    for (const member of [...members.values()].sort((a, b) => a.depth - b.depth)) {
      if (!this.visible(member)) continue;
      host.glow(member, ids.length > 135 ? 8 : 13, .95);
      if (host.hover?.kind === member.kind && host.hover.id === member.id) host.ring(member, 8);
      host.targets.push({...member, hit: 8});
    }
    host.label(projectedFocus, host.model.titleOf(focus.id), 21, true);
  }

  drawNeighborhood() {
    const {host, colors} = this;
    const focus = this.stars[host.model.groupOf(host.theorem)];
    const focal = {...this.project(focus), layer: focus.layer};
    const connected = [];
    for (const [ids, sign] of [[host.up, -1], [host.down, 1]]) {
      ids.forEach((id, i) => {
        const layer = host.model.groups[host.model.groupOf(id)][0];
        const across = (i - (ids.length - 1) / 2) * 38;
        // The dependency fan orbits with the scene. Its altitude is always the
        // declaration's defining layer, including when exploring across layers.
        const x = focus.x + sign * (140 + 27 * (i % 2));
        const z = focus.z + across + (layer - focus.layer) * 32;
        const p = this.project(tierPoint(x, z, layer));
        const star = {...p, layer, id, kind: "theorem"};
        const [from, to] = sign < 0 ? [star, focal] : [focal, star];
        host.curve(from, to, colors[layer], .73, true);
        const offset = layer === focus.layer ? -15 - (i % 2) * 10 : 14;
        connected.push({...star, hit: 13, offset, showLabel: ids.length <= (host.width < 800 ? 2 : 4)});
      });
    }
    for (const star of connected.sort((a, b) => a.depth - b.depth)) {
      host.glow(star, 20, .99);
      if (star.showLabel || host.hover?.id === star.id) host.label(star, host.model.shortName(star.id), star.offset);
      host.targets.push(star);
    }
    host.glow(focal, 70, .92);
    host.ring(focal, 16);
    host.ring(focal, 24, .3);
    host.label(focal, host.model.shortName(host.theorem), 28, true);
    this.labelLayers();
  }
}
