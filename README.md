# Artifact for the OOPSLA 2024 paper 'Qualifying System F-sub'

This GitHub repository constitutes the artifact for our paper

> Qualifying System F-Sub.  Edward Lee, Yaoyu Zhao, Ondřej Lhoták, James You, Kavin Satheeskumar, and Jonathan Immanuel Brachthäuser.
> Conditionally accepted at OOPSLA 2024.

## Overview

The artifact consists of the Coq proofs for our paper, based on the [POPLMark 08 tutorial](https://github.com/plclub/metalib) by Aydemir et al, and using lattice definitions from [Wigley 2022](https://github.com/jwiegley/coq-lattice).  There are five calculi formalized in this artifact.

1.  System Fq (in [Base](Base)), a simple, two-pointed qualifier system with no interpretation
    on qualifiers.
2.  System Fqm (in [RefImmut](RefImmut)), a two-pointed qualifier system modelling reference immutability
    (readonly/mutable).
3.  System Fqa (in [FuncColour](FuncColour)), a two-pointed qualifier system modelling function colouring
    on two colours (async/sync).
4.  System Fqc (in [CaptureTrack](CaptureTrack)), a two-pointed qualifier system modelling capture tracking
    using tracked/untracked qualifiers.  For an introduction: see [Aleksander Boruch-Gruszecki, Martin Odersky, Edward Lee, 
    Ondřej Lhoták, and Jonathan Brachthäuser. 2023. Capturing Types. ACM Trans. Program. Lang. Syst. 45, 4, 
    Article 21 (December 2023), 52 pages.](https://doi.org/10.1145/3618003)
5.  System Fq (in [ExtendedBase](ExtendedBase)), modelling a qualifier system over an arbitrary initial qualifier lattice.
 
## Getting Started -- Building Locally

This repository has a submodule for coqdocjs.  If you haven't already, run:
```
  git submodule update --init
```

We have prepared a Dockerfile to test and build our artifact locally.  To build the Docker
image containing our proof artifact and documentation, run the following command from the top-level
directory of the repository.

```
    docker build -t qualifying-fsub-proofs:local .
```

If you have Coq 8.18 installed, you can also build our proofs by running `make && make coqdoc` as well.

```
    make && make coqdoc
```

## Kick-the-Tires -- Coq proofs

In Section 4, we claim:

> The mechanization of System F<:Q (from Section 2.3), its derived calculi, System F<:QM, System F<:QA,
> and System F<:QC, (from Section 3), and extended System F<:Q (from Section 2.6), is derived from
> the mechanization of System F<: by Aydemir et al . [2008], with some inspiration taken from the
> mechanization of Lee et al. [2023] and Lee and Lhoták [2023]. All lemmas and theorems stated in
> this paper regarding these calculi have been formally mechanized, though our proofs relating the
> subqualification structure to free lattices are only proven in text, as we have found Coq’s tooling
> for universal algebra lacking.

### Definitions
Definitions for each calculus can be found in `Fsub_LetSum_Definitions.v` in each respective folder.

### Soundness Theorems / Proofs
Soundness (progress and preservation proofs) for each calculus can be found in `Fsub_LetSum_Soundness.v` in each respective folder.  In addition,
Lemma 3.7 (capture prediction) can be found as the `capture_prediction` lemma in `RefImmut/Fsub_LetSum_Soundness.v` as well.

## Pre-built proofs and documentation

While the repository contains the sources of the Coq files and the documentation
associated with the Coq proofs as well, a pre-built archive of the compiled Coq proof
can be downloaded and inspected by pulling the following automatically generated Docker image.

```
    docker pull ghcr.io/e45lee/qualifying-fsub-proofs:main
```

The Coq proofs and generated documentation can be found under `/proofs` in the generated Docker image.
To extract the pre-built proofs and documentation (into a folder called `proofs`), run:

```
    docker run -w / ghcr.io/e45lee/qualifying-fsub-proofs:main tar c proofs | tar x
```

In addition, the Coq documentation can be found online at (hopefully soon!):

<https://e45lee.github.io/qualifying-fsub-proofs/toc.html>

## Reusability Guide

In general, the base calculi (stored in [Base](Base) and [ExtendedBase](ExtendedBase)) can be reused to serve as the basis of a soundness proof
for a specific instantiation of a qualifier calculus to concrete qualifiers
and interpretations.  In particular, to construct our proofs of soundness
for our 3 dervied calculi we started from our base calculus proof and
extended it with the new terms and reduction rules -- features -- present
in each extension, taking care to assign meaningful and reasonable
interpretations of qualifiers as well, as one would do on paper as well
(See Section 2.2 of the paper).