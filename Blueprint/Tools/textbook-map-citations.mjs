// Audit each rendered citation, including entries without a mapped page.
function decodeHtml(value) {
  const named = { amp: "&", apos: "'", gt: ">", lt: "<", nbsp: "\u00a0", quot: "\"" };
  return value.replace(/&(#x[0-9a-f]+|#[0-9]+|[a-z]+);/gi, (entity, body) => {
    if (/^#x/i.test(body)) return String.fromCodePoint(Number.parseInt(body.slice(2), 16));
    if (body.startsWith("#")) return String.fromCodePoint(Number.parseInt(body.slice(1), 10));
    return named[body.toLowerCase()] ?? entity;
  });
}

export function textbookMapCitationErrors(cards, html, statementHrefByLabel) {
  const errors = [];
  const rendered = [];
  for (const match of html.matchAll(/<li\b[^>]*\bdata-leanpde-map-card="([^"]*)"[^>]*>([\s\S]*?)<\/li>/g)) {
    const content = match[2];
    const field = (name) => {
      const values = [...content.matchAll(new RegExp(`<span class="leanpde-tm-${name}">([\\s\\S]*?)<\\/span>`, "g"))];
      return values.map((value) => decodeHtml(value[1]));
    };
    rendered.push({
      label: decodeHtml(match[1]),
      pages: field("page"),
      citations: field("citation"),
      hrefs: [...content.matchAll(/<a\b[^>]*\bhref="([^"]*)"/g)].map((link) => decodeHtml(link[1])),
    });
  }
  for (const card of cards) {
    const href = statementHrefByLabel.get(card.label);
    if (!href) errors.push(`${card.label}: cited in the map but not a statement card`);
    const pages = card.page == null ? [] : [`p. ${card.page}`];
    const citations = card.citation == null ? [] : [card.citation];
    const index = rendered.findIndex((entry) =>
      entry.label === card.label
      && JSON.stringify(entry.pages) === JSON.stringify(pages)
      && JSON.stringify(entry.citations) === JSON.stringify(citations));
    if (index < 0) {
      errors.push(`${card.label}: missing rendered citation ${JSON.stringify({ page: card.page, citation: card.citation })}`);
    } else {
      const [entry] = rendered.splice(index, 1);
      if (href && !entry.hrefs.includes(href)) errors.push(`${card.label}: no link to ${href} in its map entry`);
    }
  }
  for (const entry of rendered) errors.push(`${entry.label}: unexpected rendered map citation`);
  return errors;
}
