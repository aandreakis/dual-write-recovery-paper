# Paper source

This directory mirrors the public arXiv v4 paper payload for:

> Machine-Checked Dual-Write Recovery from a Committed Log  
> Andreas Andreakis  
> arXiv:2608.00501v4

## Contents

- <code>main.tex</code> - manuscript source
- <code>main.bbl</code> - frozen bibliography generated for the public build
- <code>acmart.cls</code> - class bundled with the arXiv submission
- <code>figures/</code> - five vector-PDF figures
- <code>machine-checked-dual-write-recovery.pdf</code> - arXiv's stamped
  22-page v4 PDF

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

- [Abstract](https://arxiv.org/abs/2608.00501v4)
- [PDF](https://arxiv.org/pdf/2608.00501v4)
- [Source](https://arxiv.org/e-print/2608.00501v4)
- [DOI](https://doi.org/10.48550/arXiv.2608.00501)

The paper text and figures are licensed CC BY 4.0, matching the arXiv
posting.
