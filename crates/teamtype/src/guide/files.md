# Files and images that are not shared
(authored by agents unless marked 🧑)

TeamTypeV shares text files and binary files such as images (PNG, JPEG, PDF) alike. A file that does not reach the other person is almost always ignored. The most common case: a `.gitignore` hides your plots or screenshots.

## What is ignored

- `.teamtypev` and everything in it
- everything Git would ignore: `.gitignore` files in the shared directory and in every directory above it (even above the repository), `.git/info/exclude`, and your global Git ignore file
- everything matched by a `.teamtypevignore` file (same syntax as `.gitignore`)
- `.ignore` files, and file names ending in `~`
- version-control directories: `.git`, `.jj`, `.bzr`, `.hg`, `.pijul`, `.svn`

One exception: on the sharer, files that Git tracks are shared even when a pattern matches them.

## Make images (or anything else) appear

Put a `.teamtypevignore` file in the shared directory, or in the subdirectory the files are in. It uses `.gitignore` syntax and wins over `.gitignore`, so a `!` line brings files back:

```
!*.png
```

shares every PNG below that file's directory. To bring back only some files, name them: `!design/draft/*.png`. The same file can also hide things from TeamTypeV that Git tracks, for example `build/`.

The change takes effect within a few seconds, without restarting. If a file still does not show up, restart `teamtypev share` (or `join`) and check its output.

How to confirm: the sharer prints `Initializing binary 'plot.png' in the TeamTypeV history.` for each image it starts sharing, and the file then appears in the other person's directory. A file that is ignored produces no message at all.

`.teamtypevignore` is itself a shared file, so the other person gets the same rules.

## Viewing images

Images arrive as ordinary files in the other person's shared directory. Open them with any image viewer or an editor that can display images; TeamTypeV does not show them inside the text editor.

## Good to know

- Binary files are shared as whole files, not merged: if two people replace the same image at once, one version wins.
- Every shared file becomes part of the shared history, including its past versions. Large or frequently changing binary files make joining slower and `.teamtypev/doc` bigger. If joining feels slow, run `teamtypev guide slow`.
- Do not rely on ignore files to keep secrets from people you share with. They can delete the ignore files.
