# Yunpeng Li's research website

This folder is the source of [liyunpeng1991.github.io](https://liyunpeng1991.github.io/).
It is a checkout of the public repository
[liyunpeng1991/liyunpeng1991.github.io](https://github.com/liyunpeng1991/liyunpeng1991.github.io),
with `main` tracking `origin/main`. The root `index.html` is the homepage;
`style.css` controls its appearance; `papers/` contains the PDFs. There is
no build step.

## Publish a new paper from this project

1. Put the final PDF in `papers/` with a descriptive, versioned filename, such
   as `papers/my-result-v1.pdf`. For revisions, add `v2.pdf`, `v3.pdf`, etc.;
   never overwrite or remove an earlier PDF. The two existing unnumbered PDFs
   are their papers' website version 1 and must remain at their current paths.
2. Add one paper entry under the appropriate topic heading in `index.html`, or
   add a new topic section. Use the exact title, one plain-language sentence
   saying what problem the paper addresses and what it does, and a link to the
   current PDF or arXiv version. For a website-hosted PDF, show its posting time
   and GitHub commit. Keep superseded PDFs in `papers/` even when the homepage
   shows only the current paper entry.
3. Publish the PDF and HTML together in one commit on `main`. In Codex, you can
   simply give the PDF path and say “Publish this paper on my website”; the
   connected GitHub add-on can make the commit. From a terminal with GitHub
   access, use `git pull --ff-only`, then `git add index.html papers/`,
   `git commit -m "Publish <paper title> v1"`, and `git push origin main`.
4. Use the actual public commit's date and time (including timezone) for that
   version's “PDF posted” line. Link that line to the commit. If you do not yet
   know the commit URL, add the record immediately after publication in a
   follow-up commit. Check the live page and PDF URL after GitHub Pages deploys.

For revisions, retain earlier website PDFs and their Git history. The Cheeger
preprint now appears once on the homepage, linking to arXiv v2; its earlier
website PDFs remain in `papers/`. If a paper has a completion or manuscript
date, record that separately and only when supplied by the author. A website
upload time documents *public posting*, not the moment a proof was discovered.

GitHub Pages publishes changes pushed to the configured source branch. GitHub
says deployment can take [up to 10 minutes](https://docs.github.com/en/pages/quickstart)
after a push. The public commit and its timestamp are visible immediately on
GitHub even while the website is updating.
