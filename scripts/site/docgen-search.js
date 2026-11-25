// These listeners use the pinned doc-gen4 search UI and renderer.
async function searchDeclarations(input, results, maxResults, autocomplete) {
  const value = input.value;
  if (!value.trim()) {
    handleSearch(null, null, { target: { value: "" } }, results, maxResults, autocomplete);
    return;
  }
  results.setAttribute("state", "loading");
  let dataCenter, error;
  try {
    dataCenter = await DeclarationDataCenter.init();
  } catch (cause) {
    error = cause;
  }
  if (input.value === value) handleSearch(dataCenter, error, { target: input }, results, maxResults, autocomplete);
}

SEARCH_INPUT.addEventListener("input", debounce(() => {
  searchDeclarations(SEARCH_INPUT, ac_results, AC_MAX_RESULTS, true);
}, SEARCH_DEBOUNCE));
SEARCH_FORM.addEventListener("submit", (event) => {
  event.preventDefault();
  const value = SEARCH_INPUT.value.trim();
  const query = value ? "#" + new URLSearchParams({ q: value }) : "";
  location.href = SITE_ROOT + "search.html" + query;
});

if (SEARCH_PAGE_INPUT) {
  const search = () => searchDeclarations(SEARCH_PAGE_INPUT, SEARCH_RESULTS, SEARCH_PAGE_MAX_RESULTS, false);
  const loadQuery = () => {
    SEARCH_PAGE_INPUT.value = new URLSearchParams(location.hash.slice(1)).get("q")
      ?? new URLSearchParams(location.search).get("q") ?? "";
    search();
  };
  SEARCH_PAGE_INPUT.addEventListener("input", search);
  document.querySelectorAll(".kind_checkbox").forEach(checkbox => checkbox.addEventListener("input", search));
  window.addEventListener("hashchange", loadQuery);
  loadQuery();
}
