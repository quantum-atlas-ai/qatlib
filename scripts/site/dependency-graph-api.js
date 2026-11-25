// doc-gen4 loads search.js as a module on every API page. Resolve paths from
// this module instead of the current URL so nested declaration pages work.
export function addQatlibDependencyLinks(routes, layers, ambiguousNames = []) {
  if (!layers.some(layer => document.title.startsWith(`Qatlib.${layer}.`))) return;
  const lang = document.documentElement.lang.startsWith("en") ? "en" : "zh";
  const [graphPage, label] = routes[lang];
  const graphURL = new URL(graphPage, import.meta.url);
  const ambiguous = new Set(ambiguousNames);
  for (const declaration of document.querySelectorAll(".decl[id] > .theorem")) {
    const name = declaration.parentElement.id;
    if (name.startsWith("_private.") || ambiguous.has(name)) continue;
    const source = declaration.querySelector(":scope > .gh_link");
    if (!source) continue;
    const link = document.createElement("a");
    link.textContent = label;
    link.href = graphURL.href + "#" + new URLSearchParams({theorem: name});
    source.append(" · ", link);
  }
}
