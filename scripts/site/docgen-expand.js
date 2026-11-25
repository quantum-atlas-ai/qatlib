export function onDetailsOpen(selector, render) {
  const panels = new Set([...document.querySelectorAll(selector)].map(element => element.closest("details")));
  let pending = false;
  const load = async () => {
    if (pending || ![...panels].some(details => !details || details.open)) return;
    pending = true;
    try {
      await render();
      for (const details of panels) details?.removeEventListener("toggle", load);
    } catch (error) {
      console.error("Cannot load declaration details", error);
      pending = false;
    }
  };
  for (const details of panels) details?.addEventListener("toggle", load);
  load();
}
