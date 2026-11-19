// Progressive enhancement only: the server-rendered proofs and source links
// remain readable without JavaScript. Nothing is evaluated when a cell changes.
(() => {
  function initialize() {
    for (const notebook of document.querySelectorAll(".leanpde-notebook")) {
      const controls = notebook.querySelector(".leanpde-notebook-controls");
      const buttons = [...notebook.querySelectorAll("[data-notebook-select]")];
      const panels = [...notebook.querySelectorAll(".leanpde-notebook-example")];
      if (!controls || !buttons.length || buttons.length !== panels.length) continue;
      if (buttons.some((button) => !panels.some((panel) =>
        panel.id === button.getAttribute("aria-controls")))) continue;

      function select(button) {
        const target = button.getAttribute("aria-controls");
        for (const panel of panels) panel.hidden = panel.id !== target;
        for (const item of buttons) item.setAttribute("aria-pressed", String(item === button));
      }
      for (const button of buttons) {
        button.addEventListener("click", () => select(button));
      }
      // Honour links to a particular example, including browser back/forward.
      function selectFragment() {
        const button = buttons.find((item) =>
          `#${item.getAttribute("aria-controls")}` === location.hash);
        if (button) select(button);
        return button;
      }
      select(selectFragment() || buttons[0]);
      controls.hidden = false;
      window.addEventListener("hashchange", selectFragment);
      window.addEventListener("beforeprint", () => {
        for (const panel of panels) panel.hidden = false;
      });
      window.addEventListener("afterprint", () => {
        select(buttons.find((button) => button.getAttribute("aria-pressed") === "true") || buttons[0]);
      });
    }
  }
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initialize, { once: true });
  } else {
    initialize();
  }
})();
