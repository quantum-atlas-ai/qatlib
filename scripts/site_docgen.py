# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Adapt the mounted copy of the pinned doc-gen4 output for static hosting."""

import html
import re
import shutil
from pathlib import Path


ASSETS = Path(__file__).with_name("site")
MATHJAX_URL = "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"
POLYFILL_URL = "https://cdnjs.cloudflare.com/polyfill/v3/polyfill.min.js?features=es6"
ROOT_SCRIPT = re.compile(
    r'<script>const SITE_ROOT="([^"]+)";\s*</script>'
    r'(?:\s*<script>const MODULE_NAME="([^"]+)";\s*</script>)?'
)
INDEX_HINT = re.compile(
    r'<link rel="(?:prefetch|preload)" href="[^"]*declaration-data\.bmp"[^>]*>(?:</link>)?'
)
MASK_ICON = re.compile(r'<link rel="mask-icon"[^>]*>(?:</link>)?')
SEARCH_INIT = re.compile(r"<script>document\.getElementById\('search_page_query'\)\.value = .*?</script>", re.S)
SEARCH_ONCLICK = re.compile(r' onclick="javascript: form\.action=\'[^\']*search\.html\';"')


def patch_search(docs: Path) -> None:
    path = docs / "search.js"
    script = path.read_text(encoding="utf-8")
    start = (ASSETS / "docgen-search.js").read_text(encoding="utf-8")
    if start in script:
        return
    before, separator, eager_init = script.partition("\nDeclarationDataCenter.init()\n")
    _, closing, after = eager_init.partition("\n  });")
    if not separator or not closing:
        raise ValueError("The pinned doc-gen4 search bootstrap has changed")
    path.write_text(before + "\n\n" + start + after, encoding="utf-8")


def patch_details(docs: Path) -> None:
    jobs = {
        "instances.js": (
            "annotateInstances();\nannotateInstancesFor()",
            'onDetailsOpen(".instances-list", annotateInstances);\n'
            'onDetailsOpen(".instances-for-list", annotateInstancesFor);',
        ),
        "importedBy.js": (
            "fillImportedBy();",
            'onDetailsOpen(".imported-by-list", fillImportedBy);',
        ),
    }
    for filename, (eager, lazy) in jobs.items():
        path = docs / filename
        if not path.is_file():
            continue
        script = path.read_text(encoding="utf-8")
        if lazy in script:
            continue
        if eager not in script:
            raise ValueError(f"The pinned doc-gen4 {filename} detail loader has changed")
        script = 'import { onDetailsOpen } from "./docgen-expand.js";\n' + script.replace(eager, lazy, 1)
        path.write_text(script, encoding="utf-8")

    declarations = docs / "declaration-data.js"
    script = declarations.read_text(encoding="utf-8")
    script = script.replace(
        "DeclarationDataCenter.requestSingleton = DeclarationDataCenter.getData();",
        """DeclarationDataCenter.requestSingleton = DeclarationDataCenter.getData().catch(error => {
        DeclarationDataCenter.requestSingleton = null;
        throw error;
      });""",
    )
    declarations.write_text(script, encoding="utf-8")


def adapt_docgen(docs: Path, mathjax_dir: Path | None) -> None:
    """Defer the declaration index to search and expanded API details."""
    patch_search(docs)
    patch_details(docs)
    for name in ("docgen-bootstrap.js", "docgen-expand.js"):
        shutil.copy2(ASSETS / name, docs / name)

    needs_mathjax = False
    for page in docs.rglob("*.html"):
        source = page.read_text(encoding="utf-8")

        def bootstrap(match: re.Match[str]) -> str:
            root, module = match.groups()
            script_url = html.escape(root.rstrip("/") + "/docgen-bootstrap.js")
            attrs = f' data-site-root="{html.escape(root)}"'
            if module:
                attrs += f' data-module="{html.escape(module)}"'
            return f'<script src="{script_url}"{attrs}></script>'

        updated = ROOT_SCRIPT.sub(bootstrap, source)
        updated = SEARCH_INIT.sub("", SEARCH_ONCLICK.sub("", updated))
        updated = MASK_ICON.sub("", INDEX_HINT.sub("", updated))
        updated = re.sub(r'<script[^>]* src="' + re.escape(POLYFILL_URL) + r'"></script>', "", updated)
        if MATHJAX_URL in updated:
            needs_mathjax = True
            prefix = "../" * (len(page.relative_to(docs).parts) - 1) or "./"
            updated = updated.replace(MATHJAX_URL, prefix + "mathjax/tex-mml-chtml.js")
        if updated != source:
            page.write_text(updated, encoding="utf-8")

    style = docs / "style.css"
    css = style.read_text(encoding="utf-8")
    css = re.sub(r'(?m)^@import\s+url\([\'"]https://cdnjs\.cloudflare\.com/[^\n]+\n', "", css)
    style.write_text(css, encoding="utf-8")
    if needs_mathjax:
        if mathjax_dir is None or not (mathjax_dir / "tex-mml-chtml.js").is_file():
            raise ValueError("Provide the MathJax 3.2.2 es5 directory via --mathjax-dir")
        shutil.copytree(mathjax_dir, docs / "mathjax")
        license_file = mathjax_dir.parent / "LICENSE"
        if license_file.is_file():
            shutil.copy2(license_file, docs / "mathjax/LICENSE")
