# Progress (update after each chapter)

Done and sent (PDF in /mnt/user-data/outputs/textbook/): ch01-ch17, intA.
Coverage after ch17: 1059/1873.

Workflow per chapter:
1. Re-read REQUIREMENTS.md rules.  2. python3 tools/dump.py <modules>  (+ map/moves.tsv for theorem-level moves)
3. Write chapters/chNN.tex: usesbox, prose, theorems with \ver (Lean) / \txt (proved in text) / \ext / \num / \nogo / \opn,
   litbox, "What this chapter passes on", exercises, checklist (\chk{Module:name,...}{text}; globs allowed).
4. Forward refs: write "Chapter~N" text, never \cref to a later chapter.  5. add refs to chapters/back.tex.
6. tools/build.sh chNN  (lint + coverage + build); tools/sheet.sh chNN to view; fix overfull (use \markboth for long titles).
7. cp out/chNN.pdf /mnt/user-data/outputs/textbook/ChNN_<Title>.pdf ; SendUserFile ; commit [skip ci] + push.

Notation decisions so far: ell = sqrt(4 pi G)/g (Ch 11 eq:elldef); magnetic ansatz w (eq:magansatz); five reduced eqs
H, M, W, K_x, K_T (Ch 12); hemisphere map Q(p) = (m/E, p/E); spin connection = magnetic ansatz with w = r' (thm:spinwitten).
Interlude macros: \startinterlude{A} ... \stopinterlude (chapter counter restored).
