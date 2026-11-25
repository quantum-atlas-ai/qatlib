import {DependencyNebula} from "./dependency-nebula.js";

const root = document.querySelector(".dg");
const find = id => root.querySelector(`#dg-${id}`);
const controls = find("controls");
const list = find("list");
const filter = find("filter");
const search = find("search");
const results = find("results");
const detail = find("detail");
const sidebar = find("sidebar");
const browse = find("browse");
const status = find("status");
const tooltip = find("tooltip");
const tabs = [...root.querySelectorAll('[role="tab"]')];
const strings = JSON.parse(root.dataset.strings);
const fmt = new Intl.NumberFormat(document.documentElement.lang).format;
const layerNames = tabs.map(tab => tab.textContent);
const layerColors = tabs.map(tab => getComputedStyle(tab).getPropertyValue("--layer").trim());
const compact = matchMedia("(max-width: 799px)");
const el = (tag, className, text) => {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text) node.textContent = text;
  return node;
};
function wrapName(node, name) {
  for (const part of name.split(/([._])/u)) {
    node.append(part);
    if (part === "." || part === "_") node.append(el("wbr"));
  }
  return node;
}
const button = (className, text, action) => {
  const node = el("button", className, text);
  node.type = "button";
  node.addEventListener("click", action);
  return node;
};

async function load() {
  const response = await fetch(root.dataset.src);
  if (!response.ok) throw new Error(`HTTP ${response.status}`);
  const bytes = new Uint8Array(await response.arrayBuffer());
  const decoded = bytes[0] === 0x1f && bytes[1] === 0x8b
    ? new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"))
    : bytes;
  const data = await new Response(decoded).json();
  if (data.version !== 1 || !data.nodes.length) throw new Error("Invalid graph data");
  return data;
}

function start({groups, modules, nodes}) {
  const byName = new Map();
  const groupKey = id => `${tabs[groups[id][0]].dataset.key}/${groups[id][1]}`;
  const byGroup = new Map(groups.map((_, id) => [groupKey(id), id]));
  const groupOf = id => modules[nodes[id][1]][1];
  const titleOf = id => groups[id][2] || groups[id][1];
  const shortName = id => nodes[id][0].match(/(?:«[^»]*»|[^.]+)$/u)?.[0] || nodes[id][0];
  const members = groups.map(() => []);
  const reverse = nodes.map(() => []);
  const terms = nodes.map(([name], id) => {
    byName.set(name, id);
    members[groupOf(id)].push(id);
    return name.toLowerCase();
  });
  let edgeCount = 0;
  for (let id = 0; id < nodes.length; id++) {
    for (const target of nodes[id][2]) reverse[target].push(id);
    edgeCount += nodes[id][2].length;
  }
  const byLayer = tabs.map((_, layer) => groups.flatMap(([groupLayer], id) => groupLayer === layer ? [id] : [])
    .sort((a, b) => titleOf(a).localeCompare(titleOf(b))));
  find("totals").textContent = strings.totals.replace("{nodes}", fmt(nodes.length)).replace("{edges}", fmt(edgeCount));

  let mode = "2d";
  let tab = tabs.length - 1;
  let group;
  let theorem;
  let upstream = [];
  let downstream = [];
  const inspect = find("inspect");
  const nebula = new DependencyNebula(find("sky"), {groups, nodes, members, reverse, groupOf, titleOf, shortName, layerNames}, {
    isSidebarOpen: () => !sidebar.hidden,
    isDetailOpen: () => !detail.hidden,
    onSelect: star => star.kind === "group" ? selectGroup(star.id, true) : selectTheorem(star.id, true),
    onHover: (star, position) => {
      tooltip.hidden = !star;
      if (!star) return;
      tooltip.textContent = star.kind === "group" ? titleOf(star.id) : nodes[star.id][0];
      tooltip.style.left = Math.min(position.x + 14, Math.max(12, root.clientWidth - tooltip.offsetWidth - 12)) + "px";
      tooltip.style.top = Math.max(12, position.y - tooltip.offsetHeight - 13) + "px";
    },
  }, layerColors);

  function showSidebar(open) {
    sidebar.hidden = !open;
    browse.setAttribute("aria-expanded", open);
    if (compact.matches && open && !detail.hidden) showDetail(false);
    nebula.invalidate();
  }

  browse.addEventListener("click", () => {
    showSidebar(sidebar.hidden);
    if (!sidebar.hidden) search.focus();
  });
  compact.addEventListener("change", event => {
    if (event.matches && !detail.hidden) showSidebar(false);
    nebula.invalidate();
  });
  showSidebar(false);

  function showDetail(open) {
    detail.hidden = !open;
    inspect.hidden = open || (group === undefined && theorem === undefined);
    inspect.setAttribute("aria-expanded", open);
    nebula.invalidate();
  }

  function renderList() {
    tabs.forEach((item, id) => {
      item.setAttribute("aria-selected", id === tab);
      item.tabIndex = id === tab ? 0 : -1;
    });
    controls.setAttribute("aria-labelledby", tabs[tab].id);
    const query = filter.value.trim().toLowerCase();
    const items = byLayer[tab].filter(id => groups[id].slice(1).some(label => label.toLowerCase().includes(query)));
    list.replaceChildren(...items.map(id => {
      const label = button("dg-group", "", () => selectGroup(id));
      label.dataset.layer = tab;
      label.dataset.group = groups[id][1];
      label.setAttribute("aria-pressed", group === id);
      label.append(el("strong", "", titleOf(id)));
      const metadata = [groups[id][2] && groups[id][1], strings.layerTotal.replace("{nodes}", fmt(members[id].length))];
      label.append(el("small", "", metadata.filter(Boolean).join(" · ")));
      return label;
    }));
    if (!items.length) list.append(el("p", "dg-muted", strings.noMatches));
  }

  function nodeItem(id) {
    const label = wrapName(button("dg-node", "", () => selectTheorem(id)), shortName(id));
    label.dataset.layer = groups[groupOf(id)][0];
    label.dataset.theorem = nodes[id][0];
    label.title = nodes[id][0];
    label.setAttribute("aria-label", nodes[id][0]);
    return label;
  }

  function page(items, size, onChange = () => {}) {
    const wrapper = el("div");
    const view = el("div", "dg-nodes");
    wrapper.append(view);
    if (!items.length) {
      view.append(el("p", "dg-muted", strings.none));
      onChange([]);
      return wrapper;
    }
    let offset = 0;
    const counter = el("span");
    counter.setAttribute("aria-live", "polite");
    const prev = button("dg-mini-button", strings.previous, () => { offset -= size; drawPage(); });
    const next = button("dg-mini-button", strings.next, () => { offset += size; drawPage(); });
    function drawPage() {
      const slice = items.slice(offset, offset + size);
      view.replaceChildren(...slice.map(nodeItem));
      counter.textContent = `${fmt(offset + 1)}–${fmt(Math.min(offset + size, items.length))} / ${fmt(items.length)}`;
      prev.disabled = offset === 0;
      next.disabled = offset + size >= items.length;
      onChange(slice);
    }
    drawPage();
    if (items.length > size) {
      const pager = el("div", "dg-pager");
      pager.append(prev, next, counter);
      wrapper.append(pager);
    }
    return wrapper;
  }

  function renderSelection() {
    const scroll = list.scrollTop;
    status.hidden = true;
    renderList();
    list.scrollTop = scroll;
    detail.replaceChildren();
    showDetail(theorem !== undefined || group !== undefined);
    tooltip.hidden = true;
    upstream = downstream = [];

    if (!detail.hidden) {
      const focusedGroup = theorem === undefined ? group : groupOf(theorem);
      const layer = groups[focusedGroup][0];
      const header = el("div", "dg-inspector-head");
      const tag = el("span", "dg-layer-tag", layerNames[layer]);
      tag.dataset.layer = layer;
      const close = button("dg-mini-button", strings.close, () => {
        showDetail(false);
        inspect.focus();
      });
      header.append(tag, close);
      const heading = el("h2", "dg-selection-title");
      if (theorem === undefined) heading.textContent = titleOf(group);
      else wrapName(heading, shortName(theorem));
      heading.id = "dg-selection-title";
      heading.tabIndex = -1;
      detail.append(header, heading);
    }
    if (theorem !== undefined) {
      const [name, module, uses] = nodes[theorem];
      detail.append(wrapName(el("div", "dg-qualified-name"), name));
      const actions = el("div", "dg-inspector-actions");
      const api = el("a", "dg-api", strings.api);
      api.href = `${root.dataset.api}${modules[module][0].split("/").map(encodeURIComponent).join("/")}.html#${encodeURIComponent(name)}`;
      actions.append(api, button("dg-mini-button", strings.backToGroup, () => selectGroup(groupOf(theorem))));
      detail.append(actions);
      const up = el("section", "dg-neighbors dg-up");
      const down = el("section", "dg-neighbors dg-down");
      const replot = () => nebula.setSelection(group, theorem, upstream, downstream);
      up.append(el("h3", "", `${strings.upstream} · ${fmt(uses.length)}`),
        page(uses, 7, ids => { upstream = ids; replot(); }));
      down.append(el("h3", "", `${strings.downstream} · ${fmt(reverse[theorem].length)}`),
        page(reverse[theorem], 7, ids => { downstream = ids; replot(); }));
      detail.append(up, down);
    } else if (group !== undefined) {
      const actions = el("div", "dg-inspector-actions");
      actions.append(el("p", "dg-muted", strings.layerTotal.replace("{nodes}", fmt(members[group].length))),
        button("dg-mini-button", strings.clear, clearSelection));
      detail.append(actions, page(members[group], 18));
    }
    nebula.setSelection(group, theorem, upstream, downstream);
  }

  function updateURL() {
    const hash = new URLSearchParams();
    if (mode === "3d") hash.set("view", mode);
    if (group !== undefined) hash.set("group", groupKey(group));
    if (theorem !== undefined) hash.set("theorem", nodes[theorem][0]);
    const fragment = hash.size ? `#${hash}` : "";
    if (location.hash !== fragment) history.pushState(null, "", location.pathname + location.search + fragment);
  }

  function selectGroup(id, fromCanvas = false) {
    if (tab !== groups[id][0]) filter.value = "";
    tab = groups[id][0];
    group = id;
    theorem = undefined;
    if (compact.matches) showSidebar(false);
    updateURL();
    renderSelection();
    const focus = fromCanvas ? find("sky") : find("selection-title");
    focus?.focus({preventScroll: true});
  }

  function selectTheorem(id, fromCanvas = false) {
    const nextGroup = groupOf(id);
    const layer = groups[nextGroup][0];
    if (group !== nextGroup || tab !== layer) filter.value = "";
    group = nextGroup;
    tab = layer;
    theorem = id;
    search.value = "";
    results.hidden = true;
    if (compact.matches) showSidebar(false);
    updateURL();
    renderSelection();
    const focus = fromCanvas ? find("sky") : find("selection-title");
    focus?.focus({preventScroll: true});
  }

  function clearSelection() {
    group = theorem = undefined;
    updateURL();
    renderSelection();
  }

  function setMode(next) {
    mode = next;
    root.dataset.mode = mode;
    find("2d").setAttribute("aria-pressed", mode === "2d");
    find("3d").setAttribute("aria-pressed", mode === "3d");
    find("hint").textContent = mode === "3d" ? strings.hint3d : strings.hint2d;
    nebula.setView(mode);
  }

  for (const mode of ["2d", "3d"]) {
    find(mode).addEventListener("click", () => {
      setMode(mode);
      updateURL();
    });
  }

  function readURL() {
    const hash = new URLSearchParams(location.hash.slice(1));
    setMode(hash.get("view") === "3d" ? "3d" : "2d");
    theorem = byName.get(hash.get("theorem"));
    const nextGroup = theorem === undefined ? byGroup.get(hash.get("group")) : groupOf(theorem);
    if (nextGroup !== undefined) {
      if (group !== nextGroup || tab !== groups[nextGroup][0]) filter.value = "";
      tab = groups[nextGroup][0];
    }
    group = nextGroup;
    // Normalize older links whose group does not match the selected theorem.
    if (theorem !== undefined) hash.set("group", groupKey(group));
    const fragment = hash.size ? `#${hash}` : "";
    if (location.hash !== fragment) history.replaceState(null, "", location.pathname + location.search + fragment);
    renderSelection();
    status.hidden = !hash.has("theorem") || theorem !== undefined;
    if (!status.hidden) status.textContent = strings.missing;
  }

  const switchTab = id => {
    tab = id;
    filter.value = "";
    renderList();
    list.scrollTop = 0;
    tabs[id].focus();
  };
  tabs.forEach((item, id) => {
    item.addEventListener("click", () => switchTab(id));
    item.addEventListener("keydown", event => {
      const last = tabs.length - 1;
      const keys = {ArrowLeft: (id + last) % tabs.length, ArrowRight: (id + 1) % tabs.length, Home: 0, End: last};
      if (Object.hasOwn(keys, event.key)) {
        event.preventDefault();
        switchTab(keys[event.key]);
      }
    });
  });
  filter.addEventListener("input", () => { renderList(); list.scrollTop = 0; });
  search.addEventListener("input", () => {
    const query = search.value.trim().toLowerCase();
    results.hidden = !query;
    if (!query) return;
    const exact = terms.indexOf(query);
    const hits = exact === -1 ? [] : [exact];
    for (let id = 0; id < terms.length && hits.length < 18; id++) {
      if (id !== exact && terms[id].includes(query)) hits.push(id);
    }
    results.replaceChildren(...hits.map(id =>
      button("dg-result", nodes[id][0], () => selectTheorem(id))));
    if (!hits.length) results.append(el("p", "dg-muted", strings.noMatches));
  });
  search.addEventListener("keydown", event => {
    if (event.key === "Enter" && !results.hidden) results.querySelector("button")?.click();
    if (event.key === "ArrowDown" && !results.hidden) {
      event.preventDefault();
      results.querySelector("button")?.focus();
    }
  });
  results.addEventListener("keydown", event => {
    if (event.key !== "ArrowUp" && event.key !== "ArrowDown") return;
    event.preventDefault();
    const sibling = event.key === "ArrowUp" ? event.target.previousElementSibling : event.target.nextElementSibling;
    (sibling ?? (event.key === "ArrowUp" ? search : event.target)).focus();
  });
  sidebar.addEventListener("keydown", event => {
    if (event.key !== "Escape") return;
    if (!results.hidden && (event.target === search || results.contains(event.target))) {
      search.value = "";
      results.hidden = true;
      search.focus();
      return;
    }
    showSidebar(false);
    browse.focus();
  });
  inspect.addEventListener("click", () => {
    if (compact.matches) showSidebar(false);
    showDetail(true);
    find("selection-title")?.focus({preventScroll: true});
  });
  detail.addEventListener("keydown", event => {
    if (event.key === "Escape") {
      showDetail(false);
      inspect.focus();
    }
  });
  find("zoom-in").addEventListener("click", () => nebula.zoom(1.24));
  find("zoom-out").addEventListener("click", () => nebula.zoom(1 / 1.24));
  find("fit").addEventListener("click", () => nebula.fit());
  find("home").addEventListener("click", clearSelection);
  const fullscreen = find("fullscreen");
  fullscreen.hidden = !document.fullscreenEnabled;
  fullscreen.addEventListener("click", async () => {
    try {
      if (document.fullscreenElement) await document.exitFullscreen();
      else await root.requestFullscreen();
    } catch (error) {
      status.hidden = false;
      status.textContent = strings.fullscreenUnavailable;
    }
  });
  document.addEventListener("fullscreenchange", () => fullscreen.setAttribute("aria-pressed", Boolean(document.fullscreenElement)));
  window.addEventListener("popstate", readURL);
  find("layout").hidden = false;
  readURL();
}

load().then(start).catch(error => {
  status.textContent = strings.unavailable;
  console.error("Unable to load theorem dependency graph", error);
});
