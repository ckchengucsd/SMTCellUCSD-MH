# SMTCell (Multiheight Version)
<p align="center">
    <img src="/doc/figure/SMTCellLogo.png" width="650">
</p>
<p align="center">
    <a href="https://github.com/ckchengucsd/SMTCellUCSD/network/dependencies" alt="Contributors">
        <img src="https://img.shields.io/github/contributors/ckchengucsd/SMTCellUCSD" /></a>
    <a href="https://github.com/ckchengucsd/SMTCellUCSD/network/pulse" alt="Activity">
        <img src="https://img.shields.io/github/commit-activity/m/ckchengucsd/SMTCellUCSD" /></a>
    
</p>

_SMTCell_ is a Cell Layout Generation Toolkit for DTCO/STCO Exploration from VLSI Lab in University of California San Diego. Our goal is to enable technology exploration on FinFET, [VFET](https://github.com/ckchengucsd/SMT-based-STDCELL-Layout-Generator-for-VFET) and CFET with intuitive design rule encoding using Satisfiability Modulo Theories (SMT). Unlike our previous work, _SMTCell_ is equipped with flexibility in [**Gear Ratio (GR)**](https://github.com/ckchengucsd/SMTCellUCSD/blob/main/doc/AGR_Design.md), where metal pitch distance can be fully customized. 
Accompnany publications can be found [Gear-Ratio-Aware Standard Cell Layout Framework
for DTCO Exploration](https://vlsicad.ucsd.edu/Publications/Conferences/402/c402.pdf).

(_SMTCell_ currently is built around FinFET Technology.)

## Main Flow
<p align="center">
    <img src="/doc/figure/SMTCellMH-Flow.png" width="650">
</p>

To run our codebase, we need a customized data file called _.pinlayout_ that is converted from _.cdl_. This file comprised of basic cell design entities like pins, instances and nets. Additionally, you need to configure your own design by using _config.json_ files. To understand what each parameter is doing, please refer to documents under [HERE](https://github.com/ckchengucsd/SMTCellUCSD/tree/main/doc).

We use a SMT solver to generate a solution for the given design. The solution is then converted to a _.gdt_ file, which can be viewed using [KLayout](https://www.klayout.de/). The _.gdt_ file can be converted to _.gds_ file using [GDT2GDS](https://sourceforge.net/projects/gds2/).

## Setup Guide
### Quick Setup Guide
With [CMake(>3.18.0)](https://cmake.org/download/), you can easily compile our codebase. Please follow the steps below:
```bash
mkdir build && cd build
cmake ..
make # you should genSMTInputAGR and convSMTResult executables
cd ..
```
Our underlying SMT solver is [Z3 Prover Version 4.11.2](https://github.com/Z3Prover/z3/releases/tag/z3-4.11.2). Please follow the link, download and install the software. Alternatively, if you have Python installed, we recommend you to use `pip` for easy install. 
*(Version 4.11.2 is highly recommended. Installing any other version of Z3 Prover may cause unexpected behavior.)*

### Optional Tools and Libraries (Recommended)
_SMTCell_ depends on open source tools and libraries. Please download and install the following software if you want to enjoy the complete functionality of _SMTCell_.
- [GDT2GDS](https://sourceforge.net/projects/gds2/) for converting .gdt to .gds.
- [KLayout](https://www.klayout.de/) for viewing .gds/.lef files.
- [PROBE3.0](https://github.com/ABKGroup/PROBE3.0/) for custom PDK generation.

## Quick Start
_SMTCell_ contains three different flows. For generating
```bash
# inside the main directory
make SMTCell
# generate .gds/.lef and preview cells using Klayout
make viewSMTCell
```
## Design Your Own Cell
For setting up the cell configuration and customize cell based on your own designs, please visit this documentation [here](https://github.com/ckchengucsd/SMTCellUCSD/blob/main/doc/Design.md).

## PROBE3.0 Compatibility
PROBE3.0 is a systematic framework for design-technology pathfinding with improved design enablement. It is a powerful tool for generating custom PDKs. In _SMTCell_, we use PROBE3.0 to generate custom PDKs. We provide our Layout-vs-Schematic (LVS) deck and netlist for 2T/3T/4T cells under [here](./PROBE3.0_toolInputs).

## Releases at a Glance
- **Version 1.5** (2025/01/24)
    - Initial release of _SMTCell-MH_.
    - Allow Gear Ratio (GR) and M1 offset customization.
    - Allow customizable cell height (2 Routing Tracks, 3 Routing Tracks, 4 Routing Tracks).
    - Allow PNNP and NPPN cell generation.
    - Allow passthrough between sites (source/drain, gate).
    - Allow GDS Generation.


## Report an Issue
If you encounter any issue, please report it to us by creating an issue [here](###).

## Past Works and References (not in any particular order)
- Park, Dong Won Dissertation: [Logical Reasoning Techniques for Physical Layout in Deep Nanometer Technologies](https://escholarship.org/content/qt9mv5653s/qt9mv5653s.pdf)
- Lee, Daeyeal Dissertation: [Logical Reasoning Techniques for VLSI Applications](https://escholarship.org/content/qt7xp6p3h1/qt7xp6p3h1.pdf)
- Ho, Chia-Tung Dissertation: [Novel Computer Aided Design (CAD) Methodology for Emerging Technologies to Fight the Stagnation of Moore’s Law](https://escholarship.org/content/qt2ts172zd/qt2ts172zd.pdf)
- D. Park, I. Kang, Y. Kim, S. Gao, B. Lin, and C.K. Cheng, "ROAD: Routability Analysis and Diagnosis Framework Based on SAT Techniques," ACM/IEEE Int. Symp. on Physical Design, pp. 65-72, 2019. \[[Paper](https://dl.acm.org/doi/pdf/10.1145/3299902.3309752)\] \[[Slides](https://cseweb.ucsd.edu//~kuan/talk/placeroute18/routability.pdf)\]
- D. Park, D. Lee, I. Kang, S. Gao, B. Lin, C.K. Cheng, "SP&R: Simultaneous Placement and Routing Framework for Standard Cell Synthesis in Sub-7nm," IEEE Asia and South Pacific Design Automation, pp. 345-350, 2020. \[[Paper](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=9045729)\] \[[Slides](https://www.aspdac.com/aspdac2020/archive/pdf/5C-3.pdf)\]
- C.K. Cheng, C. Ho, D. Lee, and D. Park, "A Routability-Driven Complimentary-FET (CFET) Standard Cell Synthesis Framework using SMT," ACM/IEEE Int. Conf. on Computer-Aided Design, pp. 1-8, 2020. \[[Paper](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=9256570)\]
- D. Lee, C.T. Ho, I. Kang, S. Gao, B. Lin, and C.K. Cheng, "Many-Tier Vertical Gate-All-Around Nanowire FET Standard Cell Synthesis for Advanced Technology Nodes," IEEE Journal of Exploratory Solid-State Computational Devices and Circuits, 2021, Open Access. \[[Paper](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=9454552)\]
- C.K. Cheng, C.T. Ho, D. Lee, and B. Lin, "Multi-row Complementary-FET (CFET) Standard Cell Synthesis Framework using Satisfiability Modulo Theories (SMT)," IEEE Journal of Exploratory Solid-State Computational Devices and Circuits, 2021, Open Access. \[[Paper](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=9390403)\]
- S. Choi, J. Jung, A. B. Kahng, M. Kim, C.-H. Park, B. Pramanik, and D. Yoon, "PROBE3.0: A Systematic Framework for Design-Technology Pathfinding with Improved Design Enablement," IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems, 2023, Open Access. \[[Paper](https://ieeexplore.ieee.org/document/10322780)\]
- The PROBE3.0 Framework. \[[GitHub](https://github.com/ABKGroup/PROBE3.0)\]