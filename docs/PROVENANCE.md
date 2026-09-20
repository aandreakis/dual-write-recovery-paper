# Provenance

This repository joins two public records without changing their contents:
the arXiv paper and the Zenodo formal artifact.

## Paper record

**Title:** Machine-Checked Dual-Write Recovery from a Commit Log  
**Author:** Andreas Andreakis  
**arXiv:** [2608.00501](https://arxiv.org/abs/2608.00501)  
**arXiv DOI:** [10.48550/arXiv.2608.00501](https://doi.org/10.48550/arXiv.2608.00501)  
**Current version:** v5, 11 September 2026  
**Subjects:** cs.DB, cs.DC, cs.LO  
**License:** CC BY 4.0  
**Extent:** 23 pages, 5 figures

### Version history

| Version | Date | Public record |
|---|---|---|
| v1 | 1 Aug 2026 | [arXiv:2608.00501v1](https://arxiv.org/abs/2608.00501v1) |
| v2 | 4 Aug 2026 | [arXiv:2608.00501v2](https://arxiv.org/abs/2608.00501v2) |
| v3 | 8 Aug 2026 | [arXiv:2608.00501v3](https://arxiv.org/abs/2608.00501v3) |
| v4 | 13 Aug 2026 | [arXiv:2608.00501v4](https://arxiv.org/abs/2608.00501v4) |
| v5 | 11 Sep 2026 | [arXiv:2608.00501v5](https://arxiv.org/abs/2608.00501v5) |

Versions v1 to v4 carry the title *Machine-Checked Dual-Write Recovery from a
Committed Log*. Version v5 carries the current title.

### Repository payload

The following files under <code>paper/</code> are the payload members of
the public v5 source:

- <code>main.tex</code>
- <code>main.bbl</code>
- <code>acmart.cls</code>
- five vector PDFs under <code>figures/</code>

The public source export also supplies an arXiv-generated
<code>00README.json</code>. It is transport metadata and is not part of the
paper payload mirrored here.

The repository PDF
<code>paper/machine-checked-dual-write-recovery.pdf</code> is arXiv's v5
build, including its margin stamp.

**Public PDF SHA-256:**
<code>401bb23c5db562c385e5c13ed252a7c1a362fe11701d395e18eabe6c3808df32</code>

The source payload was compared file by file with the public arXiv v5
export on 20 September 2026. Every payload file was identical.

## Formal-artifact record

**Record title:** Isabelle/HOL formal development for "Machine-Checked
Dual-Write Recovery from a Commit Log"  
**Version:** 1.0.1  
**Publication date:** 11 September 2026  
**Version DOI:** [10.5281/zenodo.22700396](https://doi.org/10.5281/zenodo.22700396)  
**Concept DOI:** [10.5281/zenodo.21734365](https://doi.org/10.5281/zenodo.21734365)  
**License:** BSD 3-Clause  
**Archive:** <code>Dual_Write_Recovery-1.0.1.tar.gz</code>

**Archive SHA-256:**
<code>5d04755739bc111a8a339e4c3f14941b84266e17d4191e79f83490003150ca29</code>

**Zenodo MD5:**
<code>4a2857c584f6e1af7e688c20df6062c7</code>

The extracted archive contains 147 files, including 127 Isabelle theory
files across eight sessions. Its root includes the artifact README,
license, and paper-to-theorem map. The extracted tree is mirrored
verbatim as <code>formal/</code>.

The local archive was compared with the file downloaded from Zenodo on
11 September 2026. SHA-256 and MD5 both matched, and the
<code>formal/</code> tree was populated from those verified bytes.

### Previous version

**Version:** 1.0  
**Publication date:** 1 August 2026  
**Version DOI:** [10.5281/zenodo.21734366](https://doi.org/10.5281/zenodo.21734366)  
**Archive:** <code>Dual_Write_Recovery-1.0.tar.gz</code>

**Archive SHA-256:**
<code>b18fe3d6ad2a56f5f3269460ec8f87a83504ffbd006d10f3e8db25801bf3a713</code>

**Zenodo MD5:**
<code>e577b75dff4f89d3d7ba0becf15af1f9</code>

Version 1.0.1 is a documentation-only update of version 1.0. Three files
differ: <code>README.md</code>, <code>THEOREM_INDEX.md</code>, and
<code>isabelle/dual_write_layer0/document/root.bib</code>. All 127 theory
files and all eight session ROOT files are byte-identical.

## Relationship between the records

The arXiv v5 paper cites the exact formal-artifact version DOI
<code>10.5281/zenodo.22700396</code>. The arXiv v4 paper cites version 1.0,
<code>10.5281/zenodo.21734366</code>. The Zenodo record declares itself
<code>isSupplementTo</code> arXiv:2608.00501 and references the earlier
DBLog virtual-cuts formal development by DOI.

This GitHub repository is not a third archival authority. It is an
information hub that makes the two records easier to inspect together:

- Use arXiv for the paper of record.
- Use the Zenodo version DOI when you need the exact proof-artifact bytes.
- Use the Zenodo concept DOI when a citation should follow future artifact
  versions.
- Use GitHub for browsing and issue discussion.

## Derived files

The following files are derived and are not part of either archived
payload:

- <code>README.md</code>
- <code>AGENTS.md</code>
- <code>docs/</code>
- <code>CITATION.cff</code>
