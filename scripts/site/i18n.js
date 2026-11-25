export {};

const target = document.documentElement.dataset.redirectTarget;
if (target) {
  location.replace(target + location.search + location.hash);
} else {
  const menu = document.querySelector(".lang-switcher");
  if (menu) {
    const close = restoreFocus => {
      menu.open = false;
      if (restoreFocus) menu.querySelector("summary").focus();
    };
    document.addEventListener("click", event => {
      if (!menu.open) return;
      if (!menu.contains(event.target)) close(false);
      else if (event.target.closest(".lang-options a")) close(menu.contains(document.activeElement));
    });
    menu.addEventListener("keydown", event => {
      if (event.key !== "Escape" || !menu.open) return;
      event.stopPropagation();
      close(true);
    });
    for (const link of menu.querySelectorAll("[data-preserve-hash] .lang-options a")) {
      const syncHash = () => { link.hash = location.hash; };
      for (const event of ["click", "auxclick", "contextmenu"]) {
        link.addEventListener(event, syncHash);
      }
    }
  }
}
