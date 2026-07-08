# Vellvm Docs

This part of the repo holds the source for the web pages hosted at [https://vellvm.github.io/vellvm/](https://vellvm.github.io/vellvm/).

It is set up to use [Hugo](https://gohugo.io/)

## Testing locally

You should be able to host a local version of the web site (useful for testing) by running `hugo server` from this directory.


## Key components:

- `.github/workflows/hugo.yml`: specifies the workflow for deploying the site via GitHub actions

- `docs/content/*.md`: Where most of the content lives (edit those!)

   - `_index.md` is the entry page
   - `tests.md` - instructions for running test cases
   - `structure.md` - overview of the Rocq development
   - `research.md` - pointers to papers and history
   - `faq.md` - commonly asked questions
   - `news` - transient news announcements

- `docs/static/*`: folders for images, logos, static `css` code, etc.

- `docs/layouts/home.html`: HTML template for the home page

- `docs/layouts/single.html`: HTML template for the other pages

## Adding "news"

- Add an appropriately named `.md` file to the `content/news` directory.
- Put (at a minimum) a title and date field in the header of the file.

For example, the `release-2026-07-07.md` file has this header:

```
---
title: "Vellvm 3.0 Released!"
date: 2026-07-07
---
```

## Changing the style:

- See the `docs/static/css/style.css` file
