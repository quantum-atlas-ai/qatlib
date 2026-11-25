#!/usr/bin/env python3
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Check compiled theorem extraction and the dependency explorer."""

import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from build_dependency_graph import extract, lean_env, pack, write_asset
from build_site import DEPENDENCY_GRAPH_ASSET, install_dependency_graph_api

REPO = Path(__file__).resolve().parents[1]

SOURCES = {
    "Qatlib/Foundations/Basic/Identity.lean": """module
public section
namespace GraphFixture
structure Pair where
  left : Nat
  right : Nat
inductive Chain where
  | nil
  | cons (head : Nat) (tail : Chain)
def Chain.length : Chain → Nat
  | .nil => 0
  | .cons _ tail => 1 + tail.length
theorem Pair.inj : True := trivial
theorem Chain.noConfusionCustom : True := trivial
theorem Chain.sizeOf_spec : True := trivial
theorem Chain.length_eq_zero : Chain.nil.length = 0 := by simp [Chain.length]
theorem base : True := trivial
theorem identity : 1 = 1 := rfl
private theorem hidden : True := trivial
theorem isolated : True := hidden
end GraphFixture
""",
    "Qatlib/Concepts/Proofs/Combine.lean": """module
public import Qatlib.Foundations.Basic.Identity
public section
namespace GraphFixture
theorem derive (_ : identity = identity) : True := base
end GraphFixture
""",
    "Qatlib/Papers/DemoPaper/Result.lean": """module
public import Qatlib.Concepts.Proofs.Combine
public section
namespace GraphFixture
theorem main_result : True := derive rfl
end GraphFixture
""",
}


def compile_fixture(root: Path, files: dict[str, str] = SOURCES) -> list[Path]:
    """Produce actual exported, server, and private Lean module files."""
    env = {**lean_env(REPO), "LEAN_PATH": str(root)}
    for source, code in files.items():
        script = root / source
        script.parent.mkdir(parents=True, exist_ok=True)
        script.write_text(code, encoding="utf-8")
        subprocess.run(
            ["lean", "-o", str(Path(source).with_suffix(".olean")), source],
            cwd=root, env=env, check=True,
        )
    return [Path(source) for source in files]


class DependencyGraphTests(unittest.TestCase):
    def test_extract_type_and_proof_references_from_public_theorems(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = compile_fixture(root)
            graph = pack(extract(REPO, root, sources), [*sources, Path("Qatlib/Papers/Definitions/Model.lean")],
                         {"DemoPaper": "Demo paper"})
            self.assertIn([2, "Definitions", ""], graph["groups"])
            self.assertEqual(graph["version"], 1)
            self.assertIn([2, "DemoPaper", "Demo paper"], graph["groups"])
            names = [node[0] for node in graph["nodes"]]
            references = {name: {names[target] for target in ids} for name, _, ids in graph["nodes"]}
            self.assertEqual(references, {
                "GraphFixture.derive": {"GraphFixture.base", "GraphFixture.identity"},
                "GraphFixture.base": set(),
                "GraphFixture.identity": set(),
                "GraphFixture.isolated": set(),
                "GraphFixture.Pair.inj": set(),
                "GraphFixture.Chain.noConfusionCustom": set(),
                "GraphFixture.Chain.sizeOf_spec": set(),
                "GraphFixture.Chain.length_eq_zero": set(),
                "GraphFixture.main_result": {"GraphFixture.derive", "GraphFixture.identity"},
            })
            output = root / "dependencies.json.gz"
            write_asset(output, graph)
            self.assertEqual(json.loads(gzip.decompress(output.read_bytes())), graph)
            original = output.read_bytes()
            write_asset(output, graph)
            self.assertEqual(output.read_bytes(), original)

            shutil.copyfile(REPO / "lean-toolchain", root / "lean-toolchain")
            (root / "docs").mkdir()
            (root / "docs/references.bib").write_text("", encoding="utf-8")
            caller = root / "caller"
            caller.mkdir()
            subprocess.run(
                [sys.executable, str(REPO / "scripts/build_dependency_graph.py"),
                 "--repo-root", "..", "--olean-dir", "..", "--output-dir", "."],
                cwd=caller, check=True,
            )
            cli_graph = json.loads(gzip.decompress((caller / DEPENDENCY_GRAPH_ASSET).read_bytes()))
            self.assertEqual(cli_graph["nodes"], graph["nodes"])

    def test_parallel_local_instances_do_not_create_ambiguous_nodes_or_edges(self):
        files = {
            "Qatlib/Foundations/Basic/Witness.lean": """module
public section
namespace CollisionFixture
class Ready : Prop where
  evidence : True
theorem base : True := trivial
end CollisionFixture
""",
        }
        for side in ("Left", "Right"):
            files[f"Qatlib/Concepts/Proofs/{side}.lean"] = f"""module
public import Qatlib.Foundations.Basic.Witness
public section
namespace CollisionFixture
local instance shared : Ready where evidence := base
theorem from{side} : Ready := shared
theorem uses{side} : Ready := from{side}
end CollisionFixture
"""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = compile_fixture(root, files)
            records = list(extract(REPO, root, sources))
        shared = "CollisionFixture.shared"
        self.assertEqual([source for source, name, _ in records if name == shared],
                         [path.as_posix() for path in sources[1:]])
        for side in ("Left", "Right"):
            [refs] = [refs for _, name, refs in records if name == f"CollisionFixture.from{side}"]
            self.assertIn(shared, refs)
        with self.assertLogs(level="WARNING") as logs:
            graph = pack(records, sources, {})
            self.assertEqual(pack(reversed(records), sources, {}), graph)
        self.assertEqual(logs.output[0], logs.output[1])
        self.assertIn(shared, logs.output[0])
        self.assertTrue(all(path.as_posix() in logs.output[0] for path in sources[1:]))
        self.assertEqual(graph["ambiguousNames"], [shared])
        names = [node[0] for node in graph["nodes"]]
        references = {name: [names[target] for target in ids] for name, _, ids in graph["nodes"]}
        self.assertNotIn(shared, references)
        for side in ("Left", "Right"):
            self.assertEqual(references[f"CollisionFixture.from{side}"], [])
            self.assertEqual(references[f"CollisionFixture.uses{side}"], [f"CollisionFixture.from{side}"])


@unittest.skipUnless(shutil.which("node"), "Node.js is required for the dependency explorer tests")
class DependencyExplorerTests(unittest.TestCase):
    def run_node(self, program: str, cwd: Path = REPO) -> str:
        result = subprocess.run(
            ["node", "--input-type=module", "-"],
            cwd=cwd, input=program, text=True, capture_output=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_neighborhood_stars_have_distinct_hit_targets(self):
        output = self.run_node(r"""
import assert from "node:assert/strict";
import {DependencyNebula} from "./scripts/site/dependency-nebula.js";

const groups = [[0], [1], [2]];
const focusRadii = [76, 228.5, 420.5];
const stars = layer => Array.from({length: 7}, (_, i) => 7 * layer + i);
const mixed = groups.flatMap(([layer]) => stars(layer).slice(0, 2));
const noop = () => {};
globalThis.devicePixelRatio = 1;
let total = 0;

for (const [width, height] of [[1280, 720], [390, 844], [320, 568]]) {
  let minimum = Infinity;
  let cases = 0;
  for (const [focusLayer] of groups) {
    for (const [targetLayer] of groups) {
      for (let count = 1; count <= 7; count++) {
        for (let rotation = 0; rotation < 36; rotation++) {
          const angle = rotation * Math.PI / 18;
          const radius = focusRadii[focusLayer];
          const focus = {x: radius * Math.cos(angle), y: radius * Math.sin(angle), layer: focusLayer};
          const nebula = Object.assign(Object.create(DependencyNebula.prototype), {
            canvas: {clientWidth: width, clientHeight: height},
            ctx: {setTransform: noop, drawImage: noop},
            mode: "2d", colors: ["#ffffff", "#ffffff", "#ffffff"],
            handlers: {isSidebarOpen: () => false, isDetailOpen: () => true},
            groupStars: {[focusLayer]: focus}, theorem: stars(focusLayer)[0],
            model: {groups, groupOf: id => Math.floor(id / 7), shortName: String},
            backdrop: [], reducedMotion: {matches: true}, invalidate: noop,
            drawBands: noop, drawDust: noop, curve: noop, ring: noop, glow: noop, label: noop,
          });
          nebula.fit();
          nebula.camera = {...nebula.goal};
          for (const down of [stars(targetLayer), mixed]) {
            nebula.up = stars(targetLayer).slice(0, count);
            nebula.down = down;
            nebula.draw();
            assert.equal(nebula.targets.length, count + down.length);
            for (const [i, a] of nebula.targets.entries()) {
              assert.equal(nebula.hit(a.x, a.y), a);
              for (const b of nebula.targets.slice(i + 1)) {
                const distance = Math.hypot(a.x - b.x, a.y - b.y);
                assert.ok(distance > a.hit + b.hit,
                  JSON.stringify({width, height, focusLayer, targetLayer, count, rotation, distance}));
                minimum = Math.min(minimum, distance);
              }
            }
            cases++;
          }
        }
      }
    }
  }
  console.log(width + "×" + height + ": " + cases + " layouts; minimum separation " + minimum.toFixed(2) + "px");
  total += cases;
}
assert.equal(total, 13608);
""")
        print(output, end="")

    def test_cross_group_navigation_keeps_the_explorer_in_sync(self):
        self.run_node(r"""
import assert from "node:assert/strict";
import {DependencyNebula} from "./scripts/site/dependency-nebula.js";

const noop = () => {};
const context = {
  createImageData: (width, height) => ({data: new Uint8ClampedArray(width * height * 4)}),
  createRadialGradient: () => ({addColorStop: noop}),
  putImageData: noop,
  fillRect: noop,
};
class Element {
  hidden = true;
  value = "";
  children = [];
  listeners = {};
  attrs = {};
  dataset = {};
  style = {};
  writes = 0;
  clientWidth = 1280;
  clientHeight = 720;
  scrollTop = 0;

  set textContent(value) { this.text = value; this.writes++; }
  get textContent() { return this.text; }
  getContext() { return context; }
  addEventListener(event, handler) { this.listeners[event] = handler; }
  click() { this.listeners.click(); }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute(key, value) { this.attrs[key] = value; }
  focus() {}
}

function descendants(element) {
  return element.children.filter(child => child instanceof Element)
    .flatMap(child => [child, ...descendants(child)]);
}

const elements = new Map();
const find = selector => {
  if (!elements.has(selector)) elements.set(selector, new Element());
  return elements.get(selector);
};
const root = Object.assign(new Element(), {dataset: {src: "fixture", api: "./docs/"}});
const tabs = ["Foundations", "Concepts", "Papers"].map(key =>
  Object.assign(new Element(), {textContent: key, dataset: {key}}));
const palette = ["#224466", "#553311", "#a34657"];
root.querySelector = find;
root.querySelectorAll = () => tabs;
root.dataset.strings = JSON.stringify({
  totals: "{nodes} {edges}", layerTotal: "{nodes}",
  backToGroup: "Back to group", missing: "Missing",
});

globalThis.document = {
  querySelector: () => root, createElement: () => new Element(),
  documentElement: {lang: "en"}, addEventListener: noop,
};
globalThis.getComputedStyle = tab => ({getPropertyValue(key) {
  assert.equal(key, "--layer");
  return " " + palette[tabs.indexOf(tab)];
}});
globalThis.matchMedia = () => ({matches: false, addEventListener: noop});
globalThis.ResizeObserver = class { observe() {} };
globalThis.requestAnimationFrame = () => 1;
globalThis.window = new Element();
globalThis.fetch = async () => Response.json({
  version: 1, groups: [[0, "Basic", ""], [2, "Demo", ""]],
  modules: [["Qatlib/Foundations/Basic/A", 0], ["Qatlib/Papers/Demo/B", 1]],
  nodes: [["Foundation.anchor", 0, []], ["Paper.result", 1, [0]]],
});

let nebula;
const setSelection = DependencyNebula.prototype.setSelection;
DependencyNebula.prototype.setSelection = function (...args) {
  setSelection.apply(this, args);
  nebula = this;
};

const oldHash = "#group=Papers%2FDemo&theorem=Foundation.anchor";
globalThis.location = {hash: oldHash, pathname: "/dependencies.html", search: "?fixture=1"};
const historyCalls = [];
const initialSelection = new Promise(resolve => {
  const setURL = method => (_, __, url) => {
    const next = new URL(url, "https://fixture.invalid");
    historyCalls.push(method);
    assert.equal(next.search, "?fixture=1");
    location.hash = next.hash;
    resolve();
  };
  globalThis.history = {replaceState: setURL("replace"), pushState: setURL("push")};
});
await import("./scripts/site/dependency-graph.js");
await initialSelection;

const state = (key, group, layer, theorem) => {
  assert.equal(new URLSearchParams(location.hash.slice(1)).get("group"), key);
  assert.equal(tabs[layer].attrs["aria-selected"], true);
  const active = find("#dg-list").children.find(item => item.attrs["aria-pressed"]);
  assert.equal(active.dataset.group, key.split("/")[1]);
  assert.equal(nebula.group, group);
  assert.equal(nebula.theorem, theorem);
  assert.equal(nebula.goal.x, nebula.groupStars[group].x);
  assert.equal(nebula.goal.y, nebula.groupStars[group].y);
};

state("Foundations/Basic", 0, 0, 0);
assert.deepEqual(historyCalls, ["replace"]);
assert.deepEqual(nebula.colors, palette);
find("#dg-3d").click();
assert.equal(nebula.layers.colors, nebula.colors);
find("#dg-2d").click();
const search = find("#dg-search");
search.value = "Paper.result";
search.listeners.input();
find("#dg-results").children[0].click();
state("Papers/Demo", 1, 2, 1);
assert.equal(historyCalls.at(-1), "push");
const detail = find("#dg-detail");
const api = descendants(detail).find(item => item.className === "dg-api");
assert.equal(api.href, "./docs/Qatlib/Papers/Demo/B.html#Paper.result");
descendants(detail).find(item => item.dataset.theorem === "Foundation.anchor").click();
state("Foundations/Basic", 0, 0, 0);
descendants(detail).find(item => item.textContent === "Back to group").click();
state("Foundations/Basic", 0, 0, undefined);
const status = find("#dg-status");
assert.equal(status.writes, 0);
location.hash = "#theorem=unknown";
window.listeners.popstate();
assert.equal(status.hidden, false);
assert.equal(status.textContent, "Missing");
location.hash = oldHash;
window.listeners.popstate();
state("Foundations/Basic", 0, 0, 0);
assert.equal(status.hidden, true);
assert.equal(status.writes, 1);
""")

    def test_legacy_redirects_and_language_link_fragment(self):
        self.run_node(r"""
import assert from "node:assert/strict";

let sequence = 0;
const listeners = {};
const redirects = [];
const openPage = async (path, {redirectTarget, menu} = {}) => {
  const url = new URL(path, "https://example.invalid");
  globalThis.location = {
    search: url.search, hash: url.hash,
    replace: target => redirects.push(new URL(target, url).href),
  };
  globalThis.document = {
    documentElement: {dataset: {redirectTarget}},
    querySelector: () => menu,
    addEventListener: () => {},
  };
  const module = new URL("./scripts/site/i18n.js", import.meta.url);
  module.searchParams.set("fixture", String(sequence++));
  await import(module.href);
};

await openPage("/fixture-project/zh/", {redirectTarget: "../"});
assert.equal(redirects.pop(), "https://example.invalid/fixture-project/");
await openPage("/fixture-project/zh/dependencies.html?origin=old#theorem=foo",
               {redirectTarget: "../dependencies.html"});
assert.equal(redirects.pop(), "https://example.invalid/fixture-project/dependencies.html?origin=old#theorem=foo");
await openPage("/fixture-project/zh/units/Example.html#block-main",
               {redirectTarget: "../../units/Example.html"});
assert.equal(redirects.pop(), "https://example.invalid/fixture-project/units/Example.html#block-main");
await openPage("/fixture-project/");
assert.deepEqual(redirects, []);

const links = ["dependencies.html", "en/dependencies.html"].map((path, i) => {
  const link = new URL(path, "https://example.invalid/fixture-project/");
  link.addEventListener = (event, handler) => listeners[i + event] = handler;
  return link;
});
await openPage("/fixture-project/en/dependencies.html#group=Papers%2FDemo&theorem=foo&view=3d",
               {menu: {addEventListener: () => {}, querySelectorAll: () => links}});
for (const [i, link] of links.entries()) {
  for (const event of ["click", "auxclick", "contextmenu"]) {
    listeners[i + event]();
    assert.equal(link.hash, location.hash);
    link.hash = "";
  }
}
assert.deepEqual(redirects, []);
""")

    def test_api_links_use_the_portal_configuration(self):
        root = Path(tempfile.mkdtemp())
        try:
            docs = root / "docs"
            docs.mkdir()
            (docs / DEPENDENCY_GRAPH_ASSET).write_text('{"ambiguousNames": ["Qatlib.Papers.shared"]}')
            (docs / "search.js").write_text("export {};")
            install_dependency_graph_api(docs)
            self.run_node(r"""
import assert from "node:assert/strict";

const links = [];
const declaration = name => ({
  parentElement: {id: name},
  querySelector: () => ({append: (_, link) => links.push(link)}),
});
const ambiguous = "Qatlib.Papers.shared";
globalThis.document = {
  title: "Qatlib.Outside.Module",
  documentElement: {lang: "en"},
  addEventListener: () => {},
  querySelectorAll: () => ["Qatlib.Papers.lemma", "_private.sample", ambiguous].map(declaration),
  createElement: () => ({}),
};
const {addQatlibDependencyLinks} = await import("./docs/dependency-graph-api.js");
await import("./docs/search.js");
assert.equal(links.length, 0);

document.title = "Qatlib.Papers.Sample";
const routes = {
  zh: ["../dependencies.html", "定理依赖"],
  en: ["../en/dependencies.html", "dependencies"],
};
for (const [lang, expected] of [["en", "en"], ["zh-Hans", "zh"]]) {
  document.documentElement.lang = lang;
  addQatlibDependencyLinks(routes, ["Papers"], [ambiguous]);
  assert.equal(links.length, 1);
  const [link] = links.splice(0);
  const url = new URL(link.href);
  assert.equal(url.pathname, new URL(routes[expected][0], new URL("./docs/dependency-graph-api.js", import.meta.url)).pathname);
  assert.equal(new URLSearchParams(url.hash.slice(1)).get("theorem"), "Qatlib.Papers.lemma");
  assert.equal(link.textContent, routes[expected][1]);
}
""", cwd=root)
        finally:
            subprocess.run(["trash-put", "--", str(root)], check=True)


if __name__ == "__main__":
    unittest.main()
