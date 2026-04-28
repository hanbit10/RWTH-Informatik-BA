# Automated Verification of While-Programs: Empirically Comparing Dafny and Caesar

This repository contains the source code, verification examples, and comparative analysis for the Bachelor's Thesis: **"Automated Verification of While-Programs: Empirically Comparing Dafny and Caesar"** conducted at RWTH Aachen University (Informatik).

## 📌 Overview
The goal of this research is to evaluate and compare two formal verification tools:
1.  **Dafny**: A verification-ready programming language with built-in support for specification constructs.
2.  **Caesar**: A deductive verifier for the Heyvl intermediate verification language, focusing on probabilistic and quantitative reasoning.

The comparison is based on the implementation and verification of classic algorithms (While-programs) to identify the strengths, limitations, and usability of each tool.

---

## 📂 Project Structure
The verification examples are organized by algorithm as discussed in the thesis:

* **`01_LeftPad/`**: Verification of the `LeftPad` function. Includes the successful Dafny implementation and the comparative analysis between Caesar's built-in lists vs. custom Datatype lists.
* **`02_BubbleSort/`**: Implementation of the Bubble Sort algorithm. Focuses on array/list mutations and the challenges of implementing `multiset` (multiplicity) in Caesar.
* **`03_BinarySearchTree/`**: Complex data structure verification involving insertion and deletion operations.
* **`docs/`**: A copy of the thesis abstract and related preliminaries on Hoare Logic and Verification Conditions ($wlp$).

---

## 🔍 Key Comparison Points
As detailed in the thesis, the comparison covers:
* **Infrastructure**: SMT backend interactions and the Caesar/Dafny toolchains.
* **Language Features**: Support for types, collections, and predicates.
* **Proof Engineering**: Handling of loop invariants, termination (`decreases` clauses), and trigger selection.
* **Error Reporting**: How each tool assists the user in locating verification failures.

---

## 🛠 Prerequisites
To run the verification files in this repository, you will need:

### For Dafny:
* [Dafny 4.x](https://github.com/dafny-lang/dafny)
* VS Code with the [Dafny Extension](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode)

### For Caesar:
* [Caesar Verifier](https://caesarverifier.org/)
* The `heyvl` language support for your IDE.

---

## 🎓 Author
**Hanbit Chang**
RWTH Aachen University - Department of Computer Science (Informatik)
*Bachelor's Thesis*

---

### 💡 Recommendation for your README:
If you have specific results (like a comparison table), you might want to add a **"Summary of Results"** section based on Chapter 7 of your thesis to show at a glance which tool performed better in specific categories (e.g., "Dafny: Better for Multisets," "Caesar: Flexible for custom Axioms").
