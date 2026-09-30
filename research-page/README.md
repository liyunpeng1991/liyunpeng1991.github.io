# Research page for GitHub Pages

This folder is a complete static website. It contains `index.html`, `style.css`,
`.nojekyll`, and the PDF linked from the first paper. It needs no build tools.

To publish at `https://liyunpeng1991.github.io/`:

1. Sign in to GitHub and create a **public** repository named
   `liyunpeng1991.github.io`. Leave the new repository's **Add a README**
   option off; this folder already has one.
2. Upload the contents of this folder to the **root** of the repository. Keep
   `papers/sharp-higher-order-cheeger.pdf` inside the `papers` folder. Upload
   `index.html` and `style.css` as separate files at the root.
3. Open **Settings → Pages**. Under **Build and deployment**, choose
   **Deploy from a branch**, then select **main** and **/(root)**. Save.
4. Visit `https://liyunpeng1991.github.io/`. GitHub says publishing changes can take
   up to ten minutes.

The second paper links to its public arXiv record and PDF. The first paper
links to the PDF bundled here. Review the text and the PDF before you make the
repository public. Later, when the first paper has an arXiv record, you can add
a second link to that paper's `paper-links` block in `index.html`.

Official setup guide: https://docs.github.com/en/pages/quickstart
