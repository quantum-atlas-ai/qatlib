// doc-gen4 modules read these values as globals.
const docgenPage = document.currentScript.dataset;
window.SITE_ROOT = docgenPage.siteRoot;
if (docgenPage.module) window.MODULE_NAME = docgenPage.module;
