# Progress (update after each chapter)

Done (sent): front, ch01-ch31, intA, intB, full book (194 pp). Coverage 1873/1873.
Phase 2 done (sent): hand-computable proofs after every theorem/proposition/lemma/corollary in ch01-ch31, intA, intB; full book 267 pp, no overfull boxes, no undefined refs. Certificate-based results (ch14 diagonal/aligned/second stage, ch16 static classification) are marked as sketches. Statement fixes made while proving: intA Higgs label (6Q,6Y); ch13 globalform(ii) cylinder case; ch17 deltacoeff hypothesis kappa p'=S; ch18 gluedslice (i),(iii) 2D profile surface; ch19 Tolman density 3/(2g^2a^4); ch20 collapse step 2 uses F=r(1+rdot^2)+(l^2-2kappa)/r.
Coverage after intB: 1545/1873.

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
