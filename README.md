# A Complete Formal Verification of Run-Length Encoding

## Overview

This work presents the first comprehensive machine-checked verification of the run-length encoding algorithm in the Coq proof assistant, establishing correctness, optimality, and complexity properties with extraction to production-ready OCaml code. While prior formalizations exist in Agda proving basic roundtrip correctness, this development provides the first complete treatment of optimality theory, information-theoretic characterization, and practical extraction guarantees for RLE.

## Theoretical Contributions

The formalization establishes that the canonical run-length encoding is the unique minimal well-formed encoding through several fundamental theorems. The central result demonstrates that for any list, there exists a unique encoding that is simultaneously well-formed (having positive run counts and no adjacent equal values) and minimal in length. This uniqueness theorem resolves the question of whether multiple optimal encodings can exist, proving that the canonical encoder produces the sole minimal representation among all valid encodings.

The complexity analysis provides tight bounds on encoding behavior across the compression spectrum. For uniform lists of length $n$, the encoding achieves optimal $n:1$ compression by producing a single run. Conversely, for lists with no adjacent equal elements, the encoding degenerates to a 1:1 mapping where each element becomes its own unit run, representing the theoretical worst case. These bounds are proven to be tight, with concrete examples demonstrating that no compression algorithm respecting the RLE constraints can achieve better ratios.

An information-theoretic characterization frames the run count as a Kolmogorov complexity measure for RLE. The formalization proves that no encoding shorter than the run count can exist while preserving validity and well-formedness properties. This establishes run count as the fundamental lower bound for any RLE-compatible compression scheme, connecting the algorithm to deeper principles of algorithmic information theory.

## Related Work

The most closely related prior work is Masrovira's 2019 Agda formalization, which proves the fundamental roundtrip property that decoding after encoding recovers the original input. That work established termination and basic correctness but did not address optimality, minimality, uniqueness, complexity bounds, or practical extraction concerns. The present formalization extends this foundation by proving that the canonical encoding is optimal among all possible encodings, characterizing its worst-case and best-case behavior, and providing extraction with overflow protection.

Broader work in compression algorithm verification has focused primarily on Huffman coding and Lempel-Ziv variants, typically proving correctness properties without addressing optimality or complexity characterization. The four-color theorem formalization in Coq demonstrates large-scale verification of combinatorial algorithms, while projects like Compcert show that proof assistants can produce verified, efficient extracted code. This work combines both traditions by providing complete theoretical results with practical extraction guarantees.

## Implementation Features

The extraction to OCaml incorporates several practical engineering considerations absent from typical academic formalizations. The validated encoding and decoding functions include runtime bounds checking to prevent integer overflow, maintaining soundness even on 32-bit systems where OCaml's integer representation differs from Coq's mathematical naturals. The maximum representable integer is conservatively set to $2^{30} - 1$, ensuring portability across architectures.

A maxrun encoding variant supports protocols requiring bounded run lengths, such as PackBits with its 127-element limit. The streaming API provides constant-space encoding and decoding through incremental processing, formally verified to maintain equivalent semantics to batch operations while using only $O(1)$ memory regardless of input size. Type-safe interfaces for 8-bit, 16-bit, and 32-bit integers ensure that value ranges match the target application domain.

The normalization procedure proves that any sequence of runs with zero counts or adjacent equal values can be transformed to well-formed representation without changing decoded output. This enables robust handling of corrupted or non-canonical encodings, with formal proofs that sanitization preserves semantics while enforcing validity invariants.

## Proof Architecture

The development comprises approximately 5,000 lines of Coq across several interconnected modules. The core correctness section establishes the fundamental roundtrip property through auxiliary lemmas characterizing the encode-decode relationship. Well-formedness proofs demonstrate that all encodings produced by the canonical encoder satisfy positivity and no-adjacent-duplicates properties. Injectivity follows from the fact that distinct inputs produce distinct encodings, which combined with correctness implies bijectivity on the domain of well-formed encodings.

The optimality section contains the most technically demanding proofs, requiring careful induction and case analysis to show that the canonical encoding achieves minimal length. The proof strategy involves first establishing bounds on run counts for auxiliary functions, then showing these bounds are tight for the primary encoder. The uniqueness theorem combines optimality with well-formedness to conclude that any two minimal encodings must be identical.

Complexity analysis provides concrete upper and lower bounds for time and space consumption. Time complexity proofs show $O(n)$ encoding through direct counting of operations in the recursive definitions. Space analysis distinguishes between the encoding's size (bounded by input length) and the auxiliary space needed during computation (constant for streaming, linear for batch operations). The compression ratio analysis computes exact formulas for best and worst cases, with intermediate cases bounded by these extrema.

## Verification Methodology

The formalization employs standard Coq tactics including induction, case analysis, and lia for arithmetic reasoning, with minimal use of automation beyond basic simplification and rewriting. This decision prioritizes proof transparency and maintainability over conciseness, making the development accessible to readers familiar with basic proof assistant techniques but not requiring expertise in advanced automation.

All theorems are fully general, quantifying over arbitrary lists rather than restricting to finite examples or bounded inputs. The generic RLE section demonstrates that identical results hold for any type with decidable equality, establishing the algorithm's fundamental properties are independent of the specific element type. This generality comes at the cost of increased proof complexity but ensures the results transfer to any reasonable instantiation.

The test suite includes both computational checks using Coq's vm_compute reduction and formal lemmas verified through standard proof techniques. This dual approach provides both executable validation for concrete examples and mathematical guarantees for the general case. The test cases cover edge conditions including empty lists, singletons, uniform data, alternating patterns, and boundary cases for maxrun encoding.

## Extraction Configuration

The extraction process translates Coq definitions to idiomatic OCaml through careful configuration of the extraction mechanism. Native OCaml integers replace Coq's Peano naturals for arithmetic operations, with proofs ensuring this substitution preserves semantics within the validated bounds. List and option types map directly to their OCaml equivalents, while boolean operations extract to primitive comparisons.

The extraction optimization flags enable inlining of simple arithmetic and comparison functions, reducing call overhead in the generated code. Conservative type annotations prevent the extraction mechanism from introducing unsafe type casts or losing information at the Coq-to-OCaml boundary. The resulting OCaml code is suitable for integration into larger systems requiring formally verified compression components.

## Applications and Extensions

The verified RLE implementation serves as a foundation for more complex compression schemes. PackBits encoding for TIFF images corresponds to the maxrun variant with byte limits. BMP and PCX file formats use RLE as a fallback for uncompressed regions, where the verified decoder provides guaranteed correctness. The streaming API enables processing of large files without loading entire inputs into memory, valuable for embedded systems or resource-constrained environments.

Future extensions might include formalizing the interaction between RLE and entropy coding (Huffman or arithmetic), proving correctness of compressed file format decoders that combine multiple compression stages, or extending the optimality results to more sophisticated compression algorithms. The information-theoretic framework established here provides groundwork for comparing RLE against alternatives and characterizing when RLE achieves near-optimal compression.

## Conclusion

This formalization demonstrates that even seemingly simple algorithms reward rigorous verification, revealing subtle properties not apparent from informal analysis. The uniqueness of optimal encodings, the precise characterization of complexity bounds, and the connection to information theory all emerge from the proof development but might be overlooked in conventional treatments. By combining theoretical depth with practical extraction, the work shows that formal methods can produce both mathematically satisfying results and deployable implementations.

## Author

Charles C. Norton  
September 29, 2025

## Citation

```
@misc{norton2025rle,
  author = {Norton, Charles C.},
  title = {A Complete Formal Verification of Run-Length Encoding: Correctness, Optimality, and Complexity},
  year = {2025},
  howpublished = {\url{https://github.com/CharlesCNorton/RunLength-Verified}},
  note = {Formal development in Coq proof assistant}
}
```

## License

This formalization is released under the MIT License. The extracted OCaml code inherits the same license terms.

## Repository Structure

The repository contains the single formalization file `rle_encoding.v` comprising all definitions, theorems, and proofs. The extraction process generates `rle_encoding.ml` containing the executable OCaml code. Documentation and usage examples appear in this README, with the Coq source serving as the authoritative specification.

## Building

Requirements: Coq 8.18 or later with the standard library including `Lia` and list libraries.
coqc rl_encoding.v
```

This produces `rle_encoding.vo` (compiled Coq object) and `rle_encoding.ml` (extracted OCaml code). The OCaml code requires OCaml 4.12 or later and has no external dependencies beyond the standard library.
```

## Acknowledgments

This work builds on the foundational development of the Coq proof assistant by the Inria research team and the broader theorem proving community. The extraction mechanism enabling verified code generation represents decades of research in dependent type theory and compiler correctness. While this formalization contains no direct dependencies beyond Coq's standard library, it draws inspiration from the software foundations pedagogical materials and the CompCert verified compiler project's approach to extraction.
