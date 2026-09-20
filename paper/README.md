# Paper source

This directory mirrors the public arXiv v5 paper payload for:

> Machine-Checked Dual-Write Recovery from a Commit Log  
> Andreas Andreakis  
> arXiv:2608.00501v5

## Contents

- <code>main.tex</code> - manuscript source
- <code>main.bbl</code> - frozen bibliography generated for the public build
- <code>acmart.cls</code> - class bundled with the arXiv submission
- <code>figures/</code> - five vector-PDF figures
- <code>machine-checked-dual-write-recovery.pdf</code> - arXiv's stamped
  23-page v5 PDF

ArXiv's generated <code>00README.json</code> transport metadata is not
mirrored. Every paper payload member was compared file by file with the
public source export.

## Build

~~~bash
pdflatex main
pdflatex main
pdflatex main
~~~

The source bundle carries <code>main.bbl</code>, so BibTeX is not required
for the exact public rebuild.

## Public record

- [Abstract](https://arxiv.org/abs/2608.00501v5)
- [PDF](https://arxiv.org/pdf/2608.00501v5)
- [Source](https://arxiv.org/e-print/2608.00501v5)
- [DOI](https://doi.org/10.48550/arXiv.2608.00501)

The paper text and figures are licensed CC BY 4.0, matching the arXiv
posting. <code>acmart.cls</code> is the ACM class file. It keeps its own
terms, stated in its header.
