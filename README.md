# tufts-lean-seminar

Lean 4 / Mathlib project for the 
  [Fall 2026 Tufts Lean seminar](https://gmcninch.math.tufts.edu/pages/2026-Fall---lean-seminar.html).



## Setup

1. **Install `elan` (the Lean version manager) and the
   [VS Code Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).**
   You might have done this already. `elan` will fetch the correct Lean
   toolchain for this project automatically.

   ```sh
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

   See the
   [Lean installation guide](https://leanprover-community.github.io/get_started.html)
   for platform-specific instructions (including VS Code setup) if you run
   into trouble.

2. **Clone this repository.**

   ```sh
   git clone https://github.com/gmcninch-prof/tufts-lean-seminar.git
   cd tufts-lean-seminar
   ```

3. **Fetch prebuilt Mathlib binaries and build the project.**

   ```sh
   lake exe cache get
   lake build
   ```

   `lake exe cache get` downloads prebuilt `.olean` files for Mathlib and
   its dependencies, which saves you from having to compile them locally
   (this can take a very long time otherwise).

4. **Open the project in VS Code.** Open the `tufts-lean-seminar` folder
   directly (not just a single file) so the Lean 4 extension can find the
   project's `lakefile.toml`.

## Where to work

Do your own work under
[`TuftsLeanSeminar/Work`](TuftsLeanSeminar/Work/README.md). That directory
is excluded from git (aside from its `README.md`), so you can freely add,
edit, and delete `.lean` files there without ever causing a merge conflict
with the seminar repo or with other participants.

If you want to edit a file from `Lecture/` or `Homework/` (e.g. to work
through the exercises in place), **copy it into `Work/` first** and edit
the copy there, rather than editing it where it sits. That way `git pull`
never has to reconcile your edits with mine.

## If you already have your own Lean project

If you've already set up a Lean + Mathlib project of your own, you probably
don't want to keep two of them around: each project keeps its own copy of
Mathlib and its build files in a hidden `.lake/` directory, which takes up
several GB.

The easiest fix is to move your existing work into this repo:

1. Copy your `.lean` files into `TuftsLeanSeminar/Work/` (subdirectories
   are fine).

2. Fix up any imports between your own files. A file at
   `TuftsLeanSeminar/Work/Foo.lean` is imported as
   `import TuftsLeanSeminar.Work.Foo`. Imports of Mathlib
   (`import Mathlib...`) work as before.

3. Open the files in VS Code and check that they still compile. This repo
   pins a specific Mathlib version, which may differ from the one your old
   project used, so an occasional lemma may have been renamed.

4. Reclaim the disk space by deleting the `.lake/` directory in your
   *old* project:

   ```sh
   cd path/to/your-old-project
   rm -rf .lake
   ```

   This only deletes downloaded and generated files, not your own code, so
   it's safe; running `lake exe cache get` there would bring it back. (Of
   course, you can also delete the old project entirely once you're sure
   everything has been copied over.)

**A note on backups:** since `Work/` is ignored by git, nothing you put
there is version-controlled or pushed anywhere. For scratch work that's
usually fine. If you'd like your work backed up on GitHub, see
[Optional: keeping your work in your own fork](#optional-keeping-your-work-in-your-own-fork)
below.

## Staying up to date

To pull in updates from the seminar repo:

```sh
git pull
lake exe cache get
lake build
```

## Optional: keeping your work in your own fork

Nobody *needs* to do this. Working in `Work/` without version control is
the default, and it's fine for most people. But if you want your work
version-controlled and pushed to GitHub, you can use your own fork of this
repo:

1. **Fork the repo on GitHub.** Use the "Fork" button at
   <https://github.com/gmcninch-prof/tufts-lean-seminar>. This creates a
   copy under your own account, `https://github.com/<you>/tufts-lean-seminar`.

2. **Point your local clone at your fork.** If you already cloned the
   seminar repo as described above, you can keep that clone (and its
   downloaded Mathlib). Rename the existing remote to `upstream` and add
   your fork as `origin`:

   ```sh
   git remote rename origin upstream
   git remote add origin https://github.com/<you>/tufts-lean-seminar.git
   git push -u origin main
   ```

   (If you're starting fresh, clone your fork instead, then run
   `git remote add upstream https://github.com/gmcninch-prof/tufts-lean-seminar.git`.)

3. **Work in a folder of your own, not in `Work/`.** `Work/` is ignored by
   git, so files there can't be committed. Instead, create a folder such as
   `TuftsLeanSeminar/<YourName>/`. Since I'll never add anything to that
   folder, your changes there won't conflict with mine. A file
   `TuftsLeanSeminar/<YourName>/Foo.lean` is imported as
   `import TuftsLeanSeminar.<YourName>.Foo`.

4. **Commit and push your work as usual:**

   ```sh
   git add TuftsLeanSeminar/<YourName>
   git commit -m "Some progress"
   git push
   ```

5. **Get seminar updates from `upstream`**, instead of the plain
   `git pull` described above:

   ```sh
   git pull --no-rebase --no-edit upstream main
   lake exe cache get
   lake build
   git push        # optional: update your fork on GitHub too
   ```

   The `--no-rebase --no-edit` flags tell git to combine my updates with
   your commits in a merge commit, without stopping to ask how to combine
   them or opening an editor for a commit message.

The advice about not editing `Lecture/` and `Homework/` files in place
applies here too. Copy them into your own folder first.

## If something goes wrong

If you *did* edit a tracked file directly (outside `Work/`) and `git pull`
now refuses because it would overwrite your local changes, you have two
options:

* **You don't care about your edits — discard them:**

  ```sh
  git restore <path/to/file.lean>
  ```

  Then `git pull` again.

* **You want to keep your edits for later:** stash them out of the way,
  pull, and (optionally) bring them back:

  ```sh
  git stash        # sets your local changes aside
  git pull
  git stash pop    # re-applies them, on top of the update
  ```

  `git stash pop` can itself report a conflict if the file changed
  upstream in the same place you edited it. If that happens, it's usually
  easiest to just copy the piece of your work you want to keep into a new
  file under `Work/`, then `git checkout <path/to/file.lean>` to drop the
  stashed change entirely.

When in doubt, `git status` will tell you what's going on.
