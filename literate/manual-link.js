// Links the manual from every page of the literate site, which has no
// configuration for a sidebar link of its own. Every page's base href
// is the site root, and pages.yml deploys the site under literate/ of
// the manual, so "../" is the manual's root.
document.querySelector(".sidebar-content")?.prepend(
  Object.assign(document.createElement("a"),
    { href: "../", textContent: "Geb manual", className: "manual-link" }));
