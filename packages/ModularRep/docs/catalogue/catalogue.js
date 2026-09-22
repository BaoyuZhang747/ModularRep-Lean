'use strict';
const data = JSON.parse(document.getElementById('catalogue-data').textContent);
const query = document.getElementById('query');
const role = document.getElementById('role');
const statusFilter = document.getElementById('status');
const results = document.getElementById('results');
let page = 0;
const size = 40;
function render(reset) {
  if (reset) page = 0;
  const terms = query.value.toLocaleLowerCase().trim().split(/\s+/).filter(Boolean);
  const selected = data.filter(item => (!role.value || item.role === role.value) &&
    (!statusFilter.value || item.status === statusFilter.value) &&
    terms.every(term => `${item.name} ${item.path} ${item.purpose}`.toLocaleLowerCase().includes(term)));
  const totalPages = Math.max(1, Math.ceil(selected.length / size));
  page = Math.min(page, totalPages - 1);
  results.replaceChildren();
  for (const item of selected.slice(page * size, (page + 1) * size)) {
    const article = document.createElement('article');
    const heading = document.createElement('h2');
    const link = document.createElement('a');
    const name = document.createElement('code');
    name.textContent = item.name;
    link.href = item.file; link.append(name); heading.append(link);
    const purpose = document.createElement('p'); purpose.textContent = item.purpose;
    const tags = document.createElement('div'); tags.className = 'tags';
    for (const value of [item.role, item.status]) {
      const tag = document.createElement('span'); tag.textContent = value; tags.append(tag);
    }
    article.append(heading, purpose, tags); results.append(article);
  }
  document.getElementById('count').textContent = `${selected.length} of ${data.length} files`;
  document.getElementById('pages').textContent = `Page ${page + 1} of ${totalPages}`;
  document.getElementById('previous').disabled = page === 0;
  document.getElementById('next').disabled = page + 1 >= totalPages;
}
query.addEventListener('input', () => render(true));
role.addEventListener('change', () => render(true));
statusFilter.addEventListener('change', () => render(true));
document.getElementById('previous').addEventListener('click', () => { page--; render(false); });
document.getElementById('next').addEventListener('click', () => { page++; render(false); });
render(true);
