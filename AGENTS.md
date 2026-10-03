# Website maintenance instructions

This repository is the source for https://liyunpeng1991.github.io/.
The public GitHub repository is `liyunpeng1991/liyunpeng1991.github.io`.
The live site is served from the root of `main`; do not create a nested
`research-page/` directory.

When the user asks to publish or revise a paper:

1. Fetch or inspect the current remote `main` before editing, and preserve
   changes the user may have made on GitHub.
2. Copy the supplied PDF into `papers/` using a versioned filename. Never
   overwrite or remove earlier PDFs; the existing unnumbered filenames are
   website version 1 for their papers. Edit `index.html` under the appropriate
   topic section (or add one) with the exact title, a concise factual
   description, a dated PDF row for each website version, and any separately
   identified arXiv version.
3. Publish the PDF and homepage together to `main`, using Git or the connected
   GitHub add-on. Verify the remote file and the live URL.
4. Record the public commit time with its timezone as the new version's upload
   date and link to that commit. Keep earlier version dates and links intact.
   Do not present an upload time as when the author wrote or discovered the
   proof. Add a separate completion date only if the user supplies one.

Keep the static site simple and maintain its existing academic style. The
README gives the human publishing workflow.
