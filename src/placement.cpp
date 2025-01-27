#include "placement.hpp"
#include "SMTCell.hpp"
#include "format.hpp"
#include "graph.hpp"
#include "obj.hpp"

namespace bmp = boost::multiprecision;

void Placement::init_cost_var(FILE *fp) {
  fmt::print(fp, "(declare-const COST_SIZE (_ BitVec {}))\n",
             SMTCell::getBitLength_numTrackV());

  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    fmt::print(fp, "(declare-const COST_SIZE_P_SITE{} (_ BitVec {}))\n",
               site_idx, SMTCell::getBitLength_numTrackV());
    fmt::print(fp, "(declare-const COST_SIZE_N_SITE{} (_ BitVec {}))\n",
               site_idx, SMTCell::getBitLength_numTrackV());
  }
  // fmt::print(fp, "(declare-const COST_SIZE_P (_ BitVec {}))\n",
  //            SMTCell::getBitLength_numTrackV());
  // fmt::print(fp, "(declare-const COST_SIZE_N (_ BitVec {}))\n",
  //            SMTCell::getBitLength_numTrackV());

  // (metal level) cell width
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
    // skip vertical metal
    if (SMTCell::ifVertMetal(metal)) {
      continue;
    }
    fmt::print(fp, "(declare-const M{}_CELL_WIDTH (_ BitVec {}))\n", metal,
               SMTCell::getBitLength_numTrackV());

    for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      fmt::print(fp, "(declare-const M{}_COLEND_{} (_ BitVec {}))\n", metal,
                 col_idx, SMTCell::getBitLength_numTrackV());
    }
  }

  // (cell level) cell width
  fmt::print(fp, "(declare-const TOTAL_CELL_WIDTH (_ BitVec {}))\n",
             SMTCell::getBitLength_numTrackV());

  if (SMTCell::getNumMetalLayer() == 4) {
    // for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
    int metal = 4;
    for (int row_idx = 0; row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3;
         row_idx++) {
      fmt::print(fp, "(declare-const M4_TRACK_{} Bool)\n", row_idx);
    }
  }

  // fix flag
  if (SMTCell::getNumMetalLayer() == 4) {
    for (auto en : SMTCell::getExtNet()) {
      // for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
      int metal = 4;
      for (int row_idx = 0;
           row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
        fmt::print(fp, "(declare-const N{}_M4_TRACK_{} Bool)\n", en.first,
                   row_idx);
      }
      fmt::print(fp, "(declare-const N{}_M4_TRACK Bool)\n", en.first);
    }
  }

  for (auto en : SMTCell::getExtNet()) {
    // for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
    int metal = 2;
    for (int row_idx = 0; row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3;
         row_idx++) {
      fmt::print(fp, "(declare-const N{}_M2_TRACK_{} Bool)\n", en.first,
                 row_idx);
    }
    fmt::print(fp, "(declare-const N{}_M2_TRACK Bool)\n", en.first);
  }
}

void Placement::fix_placement(FILE *fp) {
  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    fmt::print(fp, "(assert (= x{} (_ bv{} {})))\n", i,
               SMTCell::getInst(i)->getInstX(),
               SMTCell::getBitLength_numTrackV());
  }
}

// LISD Flag
void Placement::init_lisd_col_var(FILE *fp) {
  int metal = 1;
  for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
       col_idx++) {
    int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
    for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
      if (SMTCell::ifSDCol_AGR(metal, col)) {
        fmt::print(fp, "(declare-const lisd_s{}m1c{} Bool)\n", site_idx, col);
      }
    }
  }
}

// GCUT FLAG
void Placement::init_gcut_col_var(FILE *fp) {
  /* Initialize marker for gate cut */
  int metal = 1;
  for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
       col_idx++) {
    int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
    for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
      if (SMTCell::ifGCol_AGR(metal, col)) {
        fmt::print(fp, "(declare-const gc_s{}m1c{} Bool)\n", site_idx, col);
      }
    }
  }
}

// Pass-through variable
void Placement::init_pass_through_col_var(FILE *fp) {
  int metal = 1;
  for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
       col_idx++) {
    int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
    fmt::print(fp, "(declare-const pt_m1c{} Bool)\n", col);
  }
}

void Placement::write_pass_through_col(int gate_passthrough,
                                       int sd_passthrough) {
  SMTCell::writeConstraint(
      fmt::format(";[All Sites] Set Pass through columns\n"));
  int from_row;
  int to_row;
  if (SMTCell::getNumTrack() == 2) {
    from_row = 1;
    to_row = 2;
  } else if (SMTCell::getNumTrack() == 3) {
    from_row = 2;
    to_row = 3;
  } else if (SMTCell::getNumTrack() == 4) {
    from_row = 3;
    to_row = 4;
  } else if (SMTCell::getNumTrack() == 5) {
    from_row = 4;
    to_row = 5;
  } else if (SMTCell::getNumTrack() == 6) {
    from_row = 5;
    to_row = 6;
  } else {
    fmt::print("ERROR: Invalid Number of Tracks\n");
  }
  for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(1) - 1;
       col_idx++) {
    int col = SMTCell::get_h_metal_col_by_idx(1, col_idx);
    if (SMTCell::ifGCol_AGR(1, col) && !gate_passthrough) {
      SMTCell::writeConstraint(
          fmt::format("(assert (= pt_m1c{} false))\n", col));
    } else if (SMTCell::ifGCol_AGR(1, col) && gate_passthrough) {
      SMTCell::writeConstraint(fmt::format(
          "(assert (ite (= pt_m1c{} true) (= M_m1r{}c{}_m1r{}c{} "
          "true) (= M_m1r{}c{}_m1r{}c{} false)))\n",
          col, from_row, col, to_row, col, from_row, col, to_row, col));
    }
    if (SMTCell::ifSDCol_AGR(1, col) && !sd_passthrough) {
      SMTCell::writeConstraint(
          fmt::format("(assert (= pt_m1c{} false))\n", col));
    } else if (SMTCell::ifSDCol_AGR(1, col) && sd_passthrough) {
      SMTCell::writeConstraint(fmt::format(
          "(assert (ite (= pt_m1c{} true) (= M_m1r{}c{}_m1r{}c{} "
          "true) (= M_m1r{}c{}_m1r{}c{} false)))\n",
          col, from_row, col, to_row, col, from_row, col, to_row, col));
    }
  }
}

void Placement::write_pass_through_col_has_gate_pin_alignment(
    std::string order_clip) {
  // for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
  SMTCell::writeConstraint(fmt::format(
      ";[All Sites] Set Pass through Gate column for {}\n", order_clip));
  int metal = 1;
  for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
       col_idx++) {
    int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
    if (!SMTCell::ifGCol_AGR(metal, col)) {
      continue;
    }
    // use tuple to store the net and the commodity
    std::vector<std::tuple<std::string, std::string>> tmp_source_sink_commodity;
    std::vector<std::tuple<int, int>> tmp_source_sink_inst;
    std::vector<std::tuple<std::string, std::string>> tmp_sink_sink_commodity;
    std::vector<std::tuple<int, int>> tmp_sink_sink_inst;
    // between source and sink instances
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // for each source with each sink
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string tmp_vname = "";
        // inst pin idx
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        // external net should NOT be considered
        if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
          continue;
        }
        // ignore startIdx and endIdx, not used
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // fmt::print("FLAG # 1 netIndex {} commodityIndex: {}\n", netIndex,
        // commodityIndex); external net should NOT be considered
        if (source_pin->getInstID() == "ext" ||
            sink_pin->getInstID() == "ext") {
          continue;
        }
        // ## Skip If Source/Sink TR is not both PMOS
        if (order_clip == "NPPN" &&
            !(source_inst_idx <= SMTCell::getLastIdxPMOS() &&
              sink_inst_idx <= SMTCell::getLastIdxPMOS())) {
          continue;
        }

        if (order_clip == "PNNP" &&
            !(source_inst_idx > SMTCell::getLastIdxPMOS() &&
              sink_inst_idx > SMTCell::getLastIdxPMOS())) {
          continue;
        }

        // ## Skip if source/sink are the same
        if (source_inst_idx == sink_inst_idx) {
          continue;
        }
        // ## Skip if either Source/Sink Pin is "Gate" Pin
        if (source_pin->getPinType() != Pin::GATE ||
            sink_pin->getPinType() != Pin::GATE) {
          continue;
        }
        // case 1: source -> 0, sink -> 1
        int row_source;
        int row_sink;
        row_source = SMTCell::get_mos_pin_row_by_site_idx(
            0, SMTCell::ifInstPMOS(source_inst_idx));
        row_sink = SMTCell::get_mos_pin_row_by_site_idx(
            1, SMTCell::ifInstPMOS(sink_inst_idx));
        Triplet vCoord_source = Triplet(metal, row_source, col);
        Triplet vCoord_sink = Triplet(metal, row_sink, col);
        std::string tmp_str_source = "";
        std::string tmp_str_sink = "";
        tmp_str_source = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_source.getVName(), pin_idx_source);
        tmp_str_sink = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_sink.getVName(), pin_idx_sink);
        // fmt::print("tmp_str_s: {}   tmp_str_t: {}\n", tmp_str_source,
        // tmp_str_sink);
        if (!SMTCell::ifAssigned(tmp_str_source) &&
            !SMTCell::ifAssigned(tmp_str_sink)) {
          SMTCell::setVar(tmp_str_source, 2);
          SMTCell::cnt("l", 3);
          SMTCell::setVar(tmp_str_sink, 2);
          SMTCell::cnt("l", 3);
          tmp_source_sink_commodity.push_back(
              std::make_tuple(tmp_str_source, tmp_str_sink));
          tmp_source_sink_inst.push_back(
              std::make_tuple(source_inst_idx, sink_inst_idx));
        }
        // case 2: source -> 1, sink -> 0
        row_source = SMTCell::get_mos_pin_row_by_site_idx(
            1, SMTCell::ifInstPMOS(source_inst_idx));
        row_sink = SMTCell::get_mos_pin_row_by_site_idx(
            0, SMTCell::ifInstPMOS(sink_inst_idx));
        vCoord_source = Triplet(metal, row_source, col);
        vCoord_sink = Triplet(metal, row_sink, col);
        tmp_str_source = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_source.getVName(), pin_idx_source);
        tmp_str_sink = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_sink.getVName(), pin_idx_sink);
        if (!SMTCell::ifAssigned(tmp_str_source) &&
            !SMTCell::ifAssigned(tmp_str_sink)) {
          SMTCell::setVar(tmp_str_source, 2);
          SMTCell::cnt("l", 3);
          SMTCell::setVar(tmp_str_sink, 2);
          SMTCell::cnt("l", 3);
          tmp_source_sink_commodity.push_back(
              std::make_tuple(tmp_str_source, tmp_str_sink));
          tmp_source_sink_inst.push_back(
              std::make_tuple(source_inst_idx, sink_inst_idx));
        }
      }
    } // end of for loop for each net
    // between sink instances
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex_1 = 0;
           commodityIndex_1 < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex_1++) {
        for (int commodityIndex_2 = commodityIndex_1;
             commodityIndex_2 < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex_2++) {
          // inst pin idx
          std::string pin_idx_sink_1 =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex_1);
          std::string pin_idx_sink_2 =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex_2);
          // external net should NOT be considered
          if (pin_idx_sink_1 == Pin::keySON || pin_idx_sink_2 == Pin::keySON) {
            continue;
          }
          // ignore startIdx and endIdx, not used
          std::shared_ptr<Pin> sink_pin_1 = SMTCell::getPin(pin_idx_sink_1);
          std::shared_ptr<Pin> sink_pin_2 = SMTCell::getPin(pin_idx_sink_2);
          // external net should NOT be considered
          if (sink_pin_1->getInstID() == "ext" ||
              sink_pin_2->getInstID() == "ext") {
            continue;
          }
          int sink_inst_1_idx = SMTCell::getPinInstIdx(sink_pin_1);
          int sink_inst_2_idx = SMTCell::getPinInstIdx(sink_pin_2);
          // ## Skip If Source/Sink TR is not both PMOS
          if (order_clip == "NPPN" &&
              !(sink_inst_1_idx <= SMTCell::getLastIdxPMOS() &&
                sink_inst_2_idx <= SMTCell::getLastIdxPMOS())) {
            continue;
          }

          if (order_clip == "PNNP" &&
              !(sink_inst_1_idx > SMTCell::getLastIdxPMOS() &&
                sink_inst_2_idx > SMTCell::getLastIdxPMOS())) {
            continue;
          }
          // ## Skip if source/sink are the same
          if (sink_inst_1_idx == sink_inst_2_idx) {
            continue;
          }
          // ## Skip if either Source/Sink Pin is "Gate" Pin
          if (sink_pin_1->getPinType() != Pin::GATE ||
              sink_pin_2->getPinType() != Pin::GATE) {
            continue;
          }
          // case 1: sink -> 0, sink -> 1
          int row_sink_1;
          int row_sink_2;
          row_sink_1 = SMTCell::get_mos_pin_row_by_site_idx(
              0, SMTCell::ifInstPMOS(sink_inst_1_idx));
          row_sink_2 = SMTCell::get_mos_pin_row_by_site_idx(
              1, SMTCell::ifInstPMOS(sink_inst_2_idx));
          Triplet vCoord_sink_1 = Triplet(metal, row_sink_1, col);
          Triplet vCoord_sink_2 = Triplet(metal, row_sink_2, col);
          std::string tmp_str_sink_1 = "";
          std::string tmp_str_sink_2 = "";
          tmp_str_sink_1 = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_1, vCoord_sink_1.getVName(), pin_idx_sink_1);
          tmp_str_sink_2 = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_2, vCoord_sink_2.getVName(), pin_idx_sink_2);

          if (!SMTCell::ifAssigned(tmp_str_sink_1) &&
              !SMTCell::ifAssigned(tmp_str_sink_2)) {
            SMTCell::setVar(tmp_str_sink_1, 2);
            SMTCell::cnt("l", 3);
            SMTCell::setVar(tmp_str_sink_2, 2);
            SMTCell::cnt("l", 3);
            tmp_sink_sink_commodity.push_back(
                std::make_tuple(tmp_str_sink_1, tmp_str_sink_2));
            tmp_sink_sink_inst.push_back(
                std::make_tuple(sink_inst_1_idx, sink_inst_2_idx));
          }
          // case 2: sink -> 1, sink -> 0
          row_sink_1 = SMTCell::get_mos_pin_row_by_site_idx(
              1, SMTCell::ifInstPMOS(sink_inst_1_idx));
          row_sink_2 = SMTCell::get_mos_pin_row_by_site_idx(
              0, SMTCell::ifInstPMOS(sink_inst_2_idx));
          vCoord_sink_1 = Triplet(metal, row_sink_1, col);
          vCoord_sink_2 = Triplet(metal, row_sink_2, col);
          std::string tmp_str_sink_1_ = "";
          std::string tmp_str_sink_2_ = "";
          tmp_str_sink_1_ = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_1, vCoord_sink_1.getVName(), pin_idx_sink_1);
          tmp_str_sink_2_ = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_2, vCoord_sink_2.getVName(), pin_idx_sink_2);
          if (!SMTCell::ifAssigned(tmp_str_sink_1_) &&
              !SMTCell::ifAssigned(tmp_str_sink_2_)) {
            SMTCell::setVar(tmp_str_sink_1_, 2);
            SMTCell::cnt("l", 3);
            SMTCell::setVar(tmp_str_sink_2_, 2);
            SMTCell::cnt("l", 3);
            tmp_sink_sink_commodity.push_back(
                std::make_tuple(tmp_str_sink_1_, tmp_str_sink_2_));
            tmp_sink_sink_inst.push_back(
                std::make_tuple(sink_inst_1_idx, sink_inst_2_idx));
          }
        }
      }
    }
    // if no variable is assigned, set the pass-through flag to false
    if (tmp_source_sink_commodity.size() == 0 &&
        tmp_sink_sink_commodity.size() == 0) {
      SMTCell::writeConstraint(
          fmt::format("(assert (and (= pt_m1c{} false)", col));
      // all nets should not pass through
      bool ifPMOS_passthrough = false;
      if (order_clip == "NPPN") {
        ifPMOS_passthrough = true;
      } else if (order_clip == "PNNP") {
        ifPMOS_passthrough = false;
      }
      for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
        SMTCell::writeConstraint(fmt::format(
            " (= N{}_E_m1r{}c{}_m1r{}c{} "
            "false)",
            SMTCell::getNet(netIndex)->getNetID(),
            SMTCell::get_mos_pin_row_by_site_idx(0, ifPMOS_passthrough), col,
            SMTCell::get_mos_pin_row_by_site_idx(1, ifPMOS_passthrough), col));
      }
      SMTCell::writeConstraint(fmt::format("))\n"));
      continue;
    }
    SMTCell::writeConstraint(
        fmt::format("(assert (ite (= pt_m1c{} true) ", col));
    SMTCell::writeConstraint("(or ");
    bool is_case_1_written = false;
    // Case 1: pin alignment between (source and sink) or (sink and sink)
    if (tmp_source_sink_commodity.size() != 0 ||
        tmp_sink_sink_commodity.size() != 0) {
      // SMTCell::writeConstraint(
      //     fmt::format("((_ at-least 1) ")); // [09/25/2024] must have pin to
      is_case_1_written = true;
    }
    if (tmp_source_sink_commodity.size() != 0) {
      for (size_t i = 0; i < tmp_source_sink_commodity.size(); i++) {
        SMTCell::writeConstraint(
            fmt::format("(and (= {} true) (= {} true)) ",
                        std::get<0>(tmp_source_sink_commodity[i]),
                        std::get<1>(tmp_source_sink_commodity[i])));
      }
    }
    if (tmp_sink_sink_commodity.size() != 0) {
      for (size_t i = 0; i < tmp_sink_sink_commodity.size(); i++) {
        SMTCell::writeConstraint(
            fmt::format("(and (= {} true) (= {} true)) ",
                        std::get<0>(tmp_sink_sink_commodity[i]),
                        std::get<1>(tmp_sink_sink_commodity[i])));
      }
    }
    if (is_case_1_written) {
      SMTCell::writeConstraint(") ");
    }
    // SMTCell::writeConstraint(")");
    // SMTCell::writeConstraint(fmt::format(" (= pt_m1c{} false)))\n", col));
    // all nets should not pass through
    SMTCell::writeConstraint("(and ");
    bool ifPMOS_passthrough = false;
    if (order_clip == "NPPN") {
      ifPMOS_passthrough = true;
    } else if (order_clip == "PNNP") {
      ifPMOS_passthrough = false;
    }
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      SMTCell::writeConstraint(fmt::format(
          " (= N{}_E_m1r{}c{}_m1r{}c{} false)",
          SMTCell::getNet(netIndex)->getNetID(),
          SMTCell::get_mos_pin_row_by_site_idx(0, ifPMOS_passthrough), col,
          SMTCell::get_mos_pin_row_by_site_idx(1, ifPMOS_passthrough), col));
    }
    SMTCell::writeConstraint(fmt::format(")))\n"));
    // else, either [row 0 and row 2] or [row 1 and row 3] or [row 1] or [row
    // 3] or [row 0] or [row 2] or nothing
  } // end of for loop for each column
  // }
}

void Placement::write_pass_through_col_has_sd_pin_alignment(
    std::string order_clip) {
  // for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
  SMTCell::writeConstraint(fmt::format(
      ";[All Sites] Set Pass through SD column for {}\n", order_clip));
  int metal = 1;
  for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
       col_idx++) {
    int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
    if (!SMTCell::ifSDCol_AGR(metal, col)) {
      continue;
    }
    // use tuple to store the net and the commodity
    std::vector<std::tuple<std::string, std::string>> tmp_source_sink_commodity;
    std::vector<std::tuple<int, int>> tmp_source_sink_inst;
    std::vector<std::tuple<std::string, std::string>> tmp_sink_sink_commodity;
    std::vector<std::tuple<int, int>> tmp_sink_sink_inst;
    // between source and sink instances
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // for each source with each sink
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string tmp_vname = "";
        // inst pin idx
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        // external net should NOT be considered
        if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
          continue;
        }
        // ignore startIdx and endIdx, not used
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // fmt::print("FLAG # 1 netIndex {} commodityIndex: {}\n", netIndex,
        // commodityIndex); external net should NOT be considered
        if (source_pin->getInstID() == "ext" ||
            sink_pin->getInstID() == "ext") {
          continue;
        }
        // ## Skip If Source/Sink TR is not both PMOS
        if (order_clip == "NPPN" &&
            !(source_inst_idx <= SMTCell::getLastIdxPMOS() &&
              sink_inst_idx <= SMTCell::getLastIdxPMOS())) {
          continue;
        }
        // ## Skip If Source/Sink TR is not both NMOS
        if (order_clip == "PNNP" &&
            !(source_inst_idx > SMTCell::getLastIdxPMOS() &&
              sink_inst_idx > SMTCell::getLastIdxPMOS())) {
          continue;
        }
        // ## Skip if source/sink are the same
        if (source_inst_idx == sink_inst_idx) {
          continue;
        }
        // ## Skip if either Source/Sink Pin is "Gate" Pin
        if (source_pin->getPinType() == Pin::GATE ||
            sink_pin->getPinType() == Pin::GATE) {
          continue;
        }
        // case 1: source -> 0, sink -> 1
        int row_source;
        int row_sink;
        row_source = SMTCell::get_mos_pin_row_by_site_idx(
            0, SMTCell::ifInstPMOS(source_inst_idx));
        row_sink = SMTCell::get_mos_pin_row_by_site_idx(
            1, SMTCell::ifInstPMOS(sink_inst_idx));
        Triplet vCoord_source = Triplet(metal, row_source, col);
        Triplet vCoord_sink = Triplet(metal, row_sink, col);
        std::string tmp_str_source = "";
        std::string tmp_str_sink = "";
        tmp_str_source = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_source.getVName(), pin_idx_source);
        tmp_str_sink = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_sink.getVName(), pin_idx_sink);
        // fmt::print("tmp_str_s: {}   tmp_str_t: {}\n", tmp_str_source,
        // tmp_str_sink);
        if (!SMTCell::ifAssigned(tmp_str_source) &&
            !SMTCell::ifAssigned(tmp_str_sink)) {
          SMTCell::setVar(tmp_str_source, 2);
          SMTCell::cnt("l", 3);
          SMTCell::setVar(tmp_str_sink, 2);
          SMTCell::cnt("l", 3);
          tmp_source_sink_commodity.push_back(
              std::make_tuple(tmp_str_source, tmp_str_sink));
          tmp_source_sink_inst.push_back(
              std::make_tuple(source_inst_idx, sink_inst_idx));
        }
        // case 2: source -> 1, sink -> 0
        row_source = SMTCell::get_mos_pin_row_by_site_idx(
            1, SMTCell::ifInstPMOS(source_inst_idx));
        row_sink = SMTCell::get_mos_pin_row_by_site_idx(
            0, SMTCell::ifInstPMOS(sink_inst_idx));
        vCoord_source = Triplet(metal, row_source, col);
        vCoord_sink = Triplet(metal, row_sink, col);
        tmp_str_source = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_source.getVName(), pin_idx_source);
        tmp_str_sink = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex, vCoord_sink.getVName(), pin_idx_sink);
        // fmt::print("tmp_str_s: {}   tmp_str_t: {}\n", tmp_str_source,
        // tmp_str_sink);
        if (!SMTCell::ifAssigned(tmp_str_source) &&
            !SMTCell::ifAssigned(tmp_str_sink)) {
          SMTCell::setVar(tmp_str_source, 2);
          SMTCell::cnt("l", 3);
          SMTCell::setVar(tmp_str_sink, 2);
          SMTCell::cnt("l", 3);
          tmp_source_sink_commodity.push_back(
              std::make_tuple(tmp_str_source, tmp_str_sink));
          tmp_source_sink_inst.push_back(
              std::make_tuple(source_inst_idx, sink_inst_idx));
        }
      }
    } // end of for loop for each net
    // between sink instances
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex_1 = 0;
           commodityIndex_1 < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex_1++) {
        for (int commodityIndex_2 = commodityIndex_1;
             commodityIndex_2 < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex_2++) {
          // inst pin idx
          std::string pin_idx_sink_1 =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex_1);
          std::string pin_idx_sink_2 =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex_2);
          // external net should NOT be considered
          if (pin_idx_sink_1 == Pin::keySON || pin_idx_sink_2 == Pin::keySON) {
            continue;
          }
          // ignore startIdx and endIdx, not used
          std::shared_ptr<Pin> sink_pin_1 = SMTCell::getPin(pin_idx_sink_1);
          std::shared_ptr<Pin> sink_pin_2 = SMTCell::getPin(pin_idx_sink_2);
          // external net should NOT be considered
          if (sink_pin_1->getInstID() == "ext" ||
              sink_pin_2->getInstID() == "ext") {
            continue;
          }
          int sink_inst_1_idx = SMTCell::getPinInstIdx(sink_pin_1);
          int sink_inst_2_idx = SMTCell::getPinInstIdx(sink_pin_2);
          // ## Skip If Source/Sink TR is not both PMOS
          if (order_clip == "NPPN" &&
              !(sink_inst_1_idx <= SMTCell::getLastIdxPMOS() &&
                sink_inst_2_idx <= SMTCell::getLastIdxPMOS())) {
            continue;
          }
          if (order_clip == "PNNP" &&
              !(sink_inst_1_idx > SMTCell::getLastIdxPMOS() &&
                sink_inst_2_idx > SMTCell::getLastIdxPMOS())) {
            continue;
          }
          // ## Skip if source/sink are the same
          if (sink_inst_1_idx == sink_inst_2_idx) {
            continue;
          }
          // ## Skip if either Source/Sink Pin is "Gate" Pin
          if (sink_pin_1->getPinType() == Pin::GATE ||
              sink_pin_2->getPinType() == Pin::GATE) {
            continue;
          }
          // case 1: sink -> 0, sink -> 1
          int row_sink_1;
          int row_sink_2;
          row_sink_1 = SMTCell::get_mos_pin_row_by_site_idx(
              0, SMTCell::ifInstPMOS(sink_inst_1_idx));
          row_sink_2 = SMTCell::get_mos_pin_row_by_site_idx(
              1, SMTCell::ifInstPMOS(sink_inst_2_idx));
          Triplet vCoord_sink_1 = Triplet(metal, row_sink_1, col);
          Triplet vCoord_sink_2 = Triplet(metal, row_sink_2, col);

          std::string tmp_str_sink_1 = "";
          std::string tmp_str_sink_2 = "";

          tmp_str_sink_1 = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_1, vCoord_sink_1.getVName(), pin_idx_sink_1);
          tmp_str_sink_2 = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_2, vCoord_sink_2.getVName(), pin_idx_sink_2);

          if (!SMTCell::ifAssigned(tmp_str_sink_1) &&
              !SMTCell::ifAssigned(tmp_str_sink_2)) {
            SMTCell::setVar(tmp_str_sink_1, 2);
            SMTCell::cnt("l", 3);
            SMTCell::setVar(tmp_str_sink_2, 2);
            SMTCell::cnt("l", 3);
            tmp_sink_sink_commodity.push_back(
                std::make_tuple(tmp_str_sink_1, tmp_str_sink_2));
            tmp_sink_sink_inst.push_back(
                std::make_tuple(sink_inst_1_idx, sink_inst_2_idx));
          }
          // case 2: sink -> 1, sink -> 0
          row_sink_1 = SMTCell::get_mos_pin_row_by_site_idx(
              1, SMTCell::ifInstPMOS(sink_inst_1_idx));
          row_sink_2 = SMTCell::get_mos_pin_row_by_site_idx(
              0, SMTCell::ifInstPMOS(sink_inst_2_idx));
          vCoord_sink_1 = Triplet(metal, row_sink_1, col);
          vCoord_sink_2 = Triplet(metal, row_sink_2, col);
          tmp_str_sink_1 = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_1, vCoord_sink_1.getVName(), pin_idx_sink_1);
          tmp_str_sink_2 = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex_2, vCoord_sink_2.getVName(), pin_idx_sink_2);

          if (!SMTCell::ifAssigned(tmp_str_sink_1) &&
              !SMTCell::ifAssigned(tmp_str_sink_2)) {
            SMTCell::setVar(tmp_str_sink_1, 2);
            SMTCell::cnt("l", 3);
            SMTCell::setVar(tmp_str_sink_2, 2);
            SMTCell::cnt("l", 3);
            tmp_sink_sink_commodity.push_back(
                std::make_tuple(tmp_str_sink_1, tmp_str_sink_2));
            tmp_sink_sink_inst.push_back(
                std::make_tuple(sink_inst_1_idx, sink_inst_2_idx));
          }
        }
      }
    }
    // if no variable is assigned, skip the pass-through flag
    bool ifPMOS_passthrough = false;
    if (order_clip == "NPPN") {
      ifPMOS_passthrough = true;
    } else if (order_clip == "PNNP") {
      ifPMOS_passthrough = false;
    }
    if (tmp_source_sink_commodity.size() == 0 &&
        tmp_sink_sink_commodity.size() == 0) {
      SMTCell::writeConstraint(
          fmt::format("(assert (and (= pt_m1c{} false)", col));
      // all nets should not pass through
      for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
        SMTCell::writeConstraint(fmt::format(
            " (= N{}_E_m1r{}c{}_m1r{}c{} "
            "false)",
            SMTCell::getNet(netIndex)->getNetID(),
            SMTCell::get_mos_pin_row_by_site_idx(0, ifPMOS_passthrough), col,
            SMTCell::get_mos_pin_row_by_site_idx(1, ifPMOS_passthrough), col));
      }
      SMTCell::writeConstraint(fmt::format("))\n"));
      continue;
    }
    SMTCell::writeConstraint(
        fmt::format("(assert (ite (= pt_m1c{} true) ", col));
    SMTCell::writeConstraint("(or ");
    bool is_case_1_written = false;
    // Case 1: pin alignment between (source and sink) or (sink and sink)
    if (tmp_source_sink_commodity.size() != 0 ||
        tmp_sink_sink_commodity.size() != 0) {
      // SMTCell::writeConstraint(
      //     fmt::format("((_ at-least 1) ")); // [09/25/2024] must have pin to
      is_case_1_written = true;
    }
    if (tmp_source_sink_commodity.size() != 0) {
      for (size_t i = 0; i < tmp_source_sink_commodity.size(); i++) {
        SMTCell::writeConstraint(
            fmt::format("(and (= {} true) (= {} true)) ",
                        std::get<0>(tmp_source_sink_commodity[i]),
                        std::get<1>(tmp_source_sink_commodity[i])));
      }
    }
    if (tmp_sink_sink_commodity.size() != 0) {
      for (size_t i = 0; i < tmp_sink_sink_commodity.size(); i++) {
        SMTCell::writeConstraint(
            fmt::format("(and (= {} true) (= {} true)) ",
                        std::get<0>(tmp_sink_sink_commodity[i]),
                        std::get<1>(tmp_sink_sink_commodity[i])));
      }
    }
    if (is_case_1_written) {
      SMTCell::writeConstraint(") ");
    }
    // SMTCell::writeConstraint(")");
    // SMTCell::writeConstraint(fmt::format(" (= pt_m1c{} false)))\n", col));
    // prohibit any pass-through from any nets
    ifPMOS_passthrough = false;
    if (order_clip == "NPPN") {
      ifPMOS_passthrough = true;
    } else if (order_clip == "PNNP") {
      ifPMOS_passthrough = false;
    }
    SMTCell::writeConstraint(fmt::format(" (and"));
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      SMTCell::writeConstraint(fmt::format(
          " (= N{}_E_m1r{}c{}_m1r{}c{} false)",
          SMTCell::getNet(netIndex)->getNetID(),
          SMTCell::get_mos_pin_row_by_site_idx(0, ifPMOS_passthrough), col,
          SMTCell::get_mos_pin_row_by_site_idx(1, ifPMOS_passthrough), col));
    }
    SMTCell::writeConstraint(fmt::format(")))\n"));
    // else, either [row 0 and row 2] or [row 1 and row 3] or [row 1] or [row
    // 3] or [row 0] or [row 2] or nothing
  } // end of for loop for each column
  // }
}

void Placement::write_gate_cut_with_two_cb_condition() {
  /* Gate cut columns must have two connections*/
  int metal = 1;
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(fmt::format(
        ";[SITE {}] Cutted gate has two CB connections\n", site_idx));
    for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
      if (!SMTCell::ifGCol_AGR(metal, col)) {
        continue;
      }
      std::vector<std::string> tmp_variables;
      std::vector<std::string> else_tmp_variables;
      int cnt_var = 0;
      int else_cnt_var = 0;
      // for (int row_idx = 0;
      //      row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
      for (auto row_idx_it = SMTCell::routing_rows_begin(site_idx);
           row_idx_it != SMTCell::routing_rows_end(site_idx); row_idx_it++) {
        int row_idx = *row_idx_it;
        int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
        std::string variable_name =
            fmt::format("M_m1r{}c{}_m2r{}c{}", row, col, row, col);
        if (!SMTCell::ifAssigned(variable_name)) {
          else_tmp_variables.push_back(variable_name);
          else_cnt_var++;
        }
        // GC FLAG do not consider non-edge rows for vias
        if (SMTCell::getNumTrack() == 2 && false) {
          // 2 track can use all rows
          continue;
        } else if (SMTCell::getNumTrack() == 3 &&
                   (row_idx == 1 || row_idx == 4)) {
          continue;
        } else if (SMTCell::getNumTrack() == 4 &&
                   (row_idx == 1 || row_idx == 2 || row_idx == 5 ||
                    row_idx == 6)) {
          continue;
        } else if (SMTCell::getNumTrack() == 5) {
          // TODO
        } else if (SMTCell::getNumTrack() == 6) {
          // TODO
        }
        if (!SMTCell::ifAssigned(variable_name)) {
          // fmt::print(fp, " {}", variable_name);
          tmp_variables.push_back(variable_name);
          SMTCell::setVar(variable_name, 2);
          SMTCell::cnt("l", 3);
          cnt_var++;
        }
      }
      // if no variable is assigned, skip the constraint
      if (cnt_var == 0) {
        continue;
      }
      SMTCell::writeConstraint(
          fmt::format("(assert (ite (= gc_s{}m1c{} true) \n", site_idx, col));
      // at-most 2 and at-least 2 constraint
      SMTCell::writeConstraint(fmt::format("\t\t(and ((_ at-most 2) "));
      for (int i = 0; i < cnt_var; i++) {
        SMTCell::writeConstraint(fmt::format("{} ", tmp_variables[i]));
      }
      SMTCell::writeConstraint(fmt::format(") ((_ at-least 2) "));
      for (int i = 0; i < cnt_var; i++) {
        SMTCell::writeConstraint(fmt::format("{} ", tmp_variables[i]));
      }
      SMTCell::writeConstraint(fmt::format(")"));
      // and also disable the middle connection
      if (SMTCell::getNumTrack() == 2) {
        if (site_idx == 0) {
          SMTCell::writeConstraint(
              fmt::format(" (= M_m1r{}c{}_m1r{}c{} false)", 0, col, 1, col));
        } else if (site_idx == 1) {
          SMTCell::writeConstraint(
              fmt::format(" (= M_m1r{}c{}_m1r{}c{} false)", 2, col, 3, col));
        }
      } else if (SMTCell::getNumTrack() == 3) {
        if (site_idx == 0) {
          SMTCell::writeConstraint(
              fmt::format(" (= M_m1r{}c{}_m1r{}c{} false)", 0, col, 1, col));
        } else if (site_idx == 1) {
          SMTCell::writeConstraint(
              fmt::format(" (= M_m1r{}c{}_m1r{}c{} false)", 3, col, 4, col));
        }
      } else if (SMTCell::getNumTrack() == 4) {
        if (site_idx == 0) {
          SMTCell::writeConstraint(
              fmt::format(" (= M_m1r{}c{}_m1r{}c{} false)", 1, col, 2, col));
        } else if (site_idx == 1) {
          SMTCell::writeConstraint(
              fmt::format(" (= M_m1r{}c{}_m1r{}c{} false)", 5, col, 6, col));
        }
      } else if (SMTCell::getNumTrack() == 5) {
        // TODO
      } else if (SMTCell::getNumTrack() == 6) {
        // TODO
      }
      SMTCell::writeConstraint(fmt::format(")\n"));
      // SMTCell::writeConstraint(fmt::format(" (= 1 1))"));
      // else at most/at least one connection can be made
      // SMTCell::writeConstraint(fmt::format("\t\t(and ((_ at-most 1) "));
      SMTCell::writeConstraint(fmt::format("\t\t((_ at-most 1) "));
      for (int i = 0; i < else_cnt_var; i++) {
        SMTCell::writeConstraint(fmt::format("{} ", else_tmp_variables[i]));
      }
      // boundary gate does not have via, so do not enforce this
      // SMTCell::writeConstraint(fmt::format(") ((_ at-least 1) "));
      // for (int i = 0; i < else_cnt_var; i++) {
      //   SMTCell::writeConstraint(fmt::format("{} ", else_tmp_variables[i]));
      // }
      // SMTCell::writeConstraint("))))\n");
      SMTCell::writeConstraint(")))\n");
    }
  }
}

void Placement::write_prohibit_gate_connection(int min_cpp) {
  /*if GC enabled, no via connects in the middle part*/
  int metal = 1;
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(fmt::format(
        ";[SITE {}] Only top and bottom via connect is allowed after "
        "gate cut + minimum gate cut nearby\n",
        site_idx));
    for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
      if (!SMTCell::ifGCol_AGR(metal, col)) {
        continue;
      }
      std::vector<std::string> tmp_variables;
      int cnt_var = 0;
      // for (int row_idx = 0;
      //      row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
      for (auto row_idx_it = SMTCell::routing_rows_begin(site_idx);
           row_idx_it != SMTCell::routing_rows_end(site_idx); row_idx_it++) {
        int row_idx = *row_idx_it;
        int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
        // record
        if (SMTCell::getNumTrack() == 2) {
          continue;
        } else if (SMTCell::getNumTrack() == 3 &&
                   (row_idx == 1 || row_idx == 4)) {
          std::string variable_name =
              fmt::format("M_m1r{}c{}_m2r{}c{}", row, col, row, col);
          if (!SMTCell::ifAssigned(variable_name)) {
            // fmt::print(fp, " {}", variable_name);
            tmp_variables.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            // SMTCell::cnt("l", 3);
            cnt_var++;
          }
        } else if (SMTCell::getNumTrack() == 4 &&
                   (row_idx == 1 || row_idx == 2 || row_idx == 5 ||
                    row_idx == 6)) {
          std::string variable_name =
              fmt::format("M_m1r{}c{}_m2r{}c{}", row, col, row, col);
          if (!SMTCell::ifAssigned(variable_name)) {
            // fmt::print(fp, " {}", variable_name);
            tmp_variables.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            // SMTCell::cnt("l", 3);
            cnt_var++;
          }
        }
      }

      // if no variable is assigned, skip the constraint
      if (cnt_var == 0) {
        continue;
      }
      SMTCell::writeConstraint(
          fmt::format("(assert (ite (= gc_s{}m1c{} true) \n", site_idx, col));
      // no middle via connection is allowed
      SMTCell::writeConstraint(fmt::format("\t\t(and"));
      for (int i = 0; i < cnt_var; i++) {
        SMTCell::writeConstraint(
            fmt::format(" (= {} false)", tmp_variables[i]));
      }
      std::string tmp_str = "";
      int tmp_cnt_var = 0;
      // reset the range to the left most
      int left_col = col - SMTCell::getMetalPitch(metal) * 2 * (min_cpp - 1);
      // shifting window on the allowable min gate cut range
      for (int tmp_col = left_col; tmp_col <= col;
           tmp_col += (SMTCell::getMetalPitch(metal) * 2)) {
        // out-of-bound detection/
        if (tmp_col <= 0) {
          continue;
        }
        int end_col =
            tmp_col + (min_cpp - 1) * SMTCell::getMetalPitch(metal) * 2;
        if (end_col > SMTCell::get_h_metal_last_col(metal)) {
          continue;
        }
        tmp_str += " (and ";
        int n_cpp = 0;
        while (n_cpp < min_cpp) {
          tmp_str +=
              fmt::format("(= gc_s{}m1c{} true)", site_idx,
                          tmp_col + SMTCell::getMetalPitch(metal) * 2 * n_cpp);
          n_cpp++;
        }
        tmp_str += ")";
        tmp_cnt_var++;
      }
      if (tmp_cnt_var > 0) {
        SMTCell::writeConstraint(" (or");
        SMTCell::writeConstraint(tmp_str);
        SMTCell::writeConstraint(")");
      }
      SMTCell::writeConstraint(fmt::format(")"));
      // else, nothing?
      SMTCell::writeConstraint(fmt::format(" (= 1 1)"));
      SMTCell::writeConstraint("))\n");
    }
  }
}

void Placement::write_limit_lisd_gc_pt_var_by_cost_size() {
  // fmt::print(fp, "; Limit LISD & GC Variables by Cost Size\n");
  SMTCell::writeConstraint("; Limit LISD & GC & PT Variables by Cost Size\n");
  int metal = 1;
  // skip the right most column
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    for (int col_idx = 0; col_idx < SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      SMTCell::writeConstraint(
          fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (and",
                      col_idx, SMTCell::getBitLength_numTrackV()));
      // iterate remaining columns and set the lisd/gcut to false
      for (int remain_col_idx = col_idx + 1;
           remain_col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
           remain_col_idx++) {
        int remain_col = SMTCell::get_h_metal_col_by_idx(metal, remain_col_idx);
        SMTCell::writeConstraint(
            fmt::format(" (= pt_m1c{} false)", remain_col));
        if (SMTCell::ifGCol_AGR(metal, remain_col)) {
          // fmt::print(fp, "(= gc_m1c{} false)\n", remain_col);
          SMTCell::writeConstraint(
              fmt::format(" (= gc_s{}m1c{} false)", site_idx, remain_col));
        } else if (SMTCell::ifSDCol_AGR(metal, remain_col) &&
                   SMTCell::is_lisd_col(site_idx, remain_col)) {
          // fmt::print(fp, "(= lisd_m1c{} false)\n", remain_col);
          SMTCell::writeConstraint(
              fmt::format(" (= lisd_s{}m1c{} false)", site_idx, remain_col));
        }
      }
      SMTCell::writeConstraint(") (= 1 1)))\n");
    }
  }
}

// LISD Flag
void Placement::write_lisd_col_has_only_one_connection() {
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(
        fmt::format(";[SITE {}] lisd enables middle connections \n", site_idx));
    int metal = 1;
    // 1. Enforce only one of the via in the same column can be used
    // index start with 1 since we skip the first column
    // at most one of the vias in the same column can be used
    SMTCell::is_lisd_col_empty(); // check if there is any lisd column
    for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
      if (!SMTCell::ifSDCol_AGR(metal, col)) {
        continue;
      }
      if (!SMTCell::is_lisd_col(site_idx, col)) {
        continue;
      }
      std::vector<std::string> tmp_variables;
      int cnt_var = 0;
      // for (int row_idx = 0;
      //      row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
      for (auto row_idx_it = SMTCell::routing_rows_begin(site_idx);
           row_idx_it != SMTCell::routing_rows_end(site_idx); row_idx_it++) {
        int row_idx = *row_idx_it;
        int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
        // fmt::print(fp, " M_m1r{}c{}_m2r{}c{}", row, col, row, col);
        std::string variable_name =
            fmt::format("M_m1r{}c{}_m2r{}c{}", row, col, row, col);
        if (!SMTCell::ifAssigned(variable_name)) {
          // fmt::print(fp, " {}", variable_name);
          tmp_variables.push_back(variable_name);
          SMTCell::setVar(variable_name, 2);
          SMTCell::cnt("l", 3);
          cnt_var++;
        }
      }
      // if no variable is assigned, skip the constraint
      if (cnt_var == 0) {
        continue;
      }
      SMTCell::writeConstraint(
          fmt::format("(assert (ite (= lisd_s{}m1c{} true) \n", site_idx, col));
      // at-most 1 and at-least 1 constraint
      SMTCell::writeConstraint(fmt::format("\t\t(and ((_ at-most 1) "));
      for (int i = 0; i < cnt_var; i++) {
        SMTCell::writeConstraint(fmt::format("{} ", tmp_variables[i]));
      }
      SMTCell::writeConstraint(fmt::format(") ((_ at-least 1) "));
      for (int i = 0; i < cnt_var; i++) {
        SMTCell::writeConstraint(fmt::format("{} ", tmp_variables[i]));
      }
      SMTCell::writeConstraint(fmt::format(")) \n"));

      // else disable the middle row because neither instance can build vias
      // there
      if (SMTCell::getNumTrack() == 2) {
        // SMTCell::writeConstraint("\t\t(= 1 1)");
        // SMTCell::writeConstraint(fmt::format("\t\t(= M_m1r0c{}_m1r1c{}
        // false)", col, col));
        if (site_idx == 0) {
          SMTCell::writeConstraint(
              fmt::format("\t\t(= M_m1r0c{}_m1r1c{} false)", col, col));
        } else if (site_idx == 1) {
          SMTCell::writeConstraint(
              fmt::format("\t\t(= M_m1r2c{}_m1r3c{} false)", col, col));
        }
        SMTCell::writeConstraint(")");
      } else if (SMTCell::getNumTrack() == 3) {
        // LISD FLAG: disable only the middle part?
        if (site_idx == 0) {
          SMTCell::writeConstraint("\t\t(and ");
          SMTCell::writeConstraint(
              fmt::format("(= M_m1r0c{}_m1r1c{} false) (= M_m1r1c{}_m2r1c{} "
                          "false) (= M_m1r1c{}_m1r2c{} false)",
                          col, col, col, col, col, col));
          SMTCell::writeConstraint("))");
          // SMTCell::writeConstraint(")");
        } else if (site_idx == 1) {
          SMTCell::writeConstraint("\t\t(and ");
          SMTCell::writeConstraint(
              fmt::format("(= M_m1r3c{}_m1r4c{} false) (= M_m1r4c{}_m2r4c{} "
                          "false) (= M_m1r4c{}_m1r5c{} false)",
                          col, col, col, col, col, col));
          SMTCell::writeConstraint("))");
          // SMTCell::writeConstraint(")");
        }
      } else if (SMTCell::getNumTrack() == 4) {
        SMTCell::writeConstraint("\t\t(and ");
        // LISD FLAG: disable only the middle part?
        if (site_idx == 0) {
          std::string middle_metal =
              fmt::format("M_m1r{}c{}_m1r{}c{}", 1, col, 2, col);
          // SMTCell::writeConstraint(
          //     fmt::format("(= M_m1r{}c{}_m1r{}c{} false)", 1, col, 2, col));
          if (!SMTCell::ifAssigned(middle_metal)) {
            SMTCell::setVar(middle_metal, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(
                fmt::format(" (= {} false)", middle_metal));
          }
          // [10/04/2024] LISD FLAG: avoid duplicated via connections
          SMTCell::writeConstraint("(and");
          // if lisd is not true, pmos can only connect to the one top via
          std::string first_via =
              fmt::format("M_m1r{}c{}_m2r{}c{}", 0, col, 0, col);
          std::string second_via =
              fmt::format("M_m1r{}c{}_m2r{}c{}", 1, col, 1, col);
          // SMTCell::writeConstraint(
          //     fmt::format(" ((_ at-most 1) (= M_m1r{}c{}_m2r{}c{} true) (= "
          //                 "M_m1r{}c{}_m2r{}c{} true))",
          //                 0, col, 0, col, 1, col, 1, col));
          SMTCell::writeConstraint(fmt::format(" ((_ at-most 1)"));
          if (!SMTCell::ifAssigned(first_via)) {
            SMTCell::setVar(first_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", first_via));
          }
          if (!SMTCell::ifAssigned(second_via)) {
            SMTCell::setVar(second_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", second_via));
          }
          SMTCell::writeConstraint(")");
          // if lisd is not true, nmos can only connect to the one bottom via
          first_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 2, col, 2, col);
          second_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 3, col, 3, col);
          // SMTCell::writeConstraint(
          //     fmt::format(" ((_ at-most 1) (= M_m1r{}c{}_m2r{}c{} true) (= "
          //                 "M_m1r{}c{}_m2r{}c{} true))",
          //                 2, col, 2, col, 3, col, 3, col));
          SMTCell::writeConstraint(fmt::format(" ((_ at-most 1)"));
          if (!SMTCell::ifAssigned(first_via)) {
            SMTCell::setVar(first_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", first_via));
          }
          if (!SMTCell::ifAssigned(second_via)) {
            SMTCell::setVar(second_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", second_via));
          }
          SMTCell::writeConstraint(")");
          // [08/07/2024] LISD FLAG: avoid via sitting too close
          first_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 1, col, 1, col);
          second_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 2, col, 2, col);
          // SMTCell::writeConstraint(
          //     fmt::format(" ((_ at-most 1) (= M_m1r{}c{}_m2r{}c{} true) (= "
          //                 "M_m1r{}c{}_m2r{}c{} true))",
          //                 1, col, 1, col, 2, col, 2, col));
          SMTCell::writeConstraint(fmt::format(" ((_ at-most 1)"));
          if (!SMTCell::ifAssigned(first_via)) {
            SMTCell::setVar(first_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", first_via));
          }
          if (!SMTCell::ifAssigned(second_via)) {
            SMTCell::setVar(second_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", second_via));
          }
          SMTCell::writeConstraint(")");
        } else if (site_idx == 1) {
          std::string middle_metal =
              fmt::format("M_m1r{}c{}_m1r{}c{}", 5, col, 6, col);
          // SMTCell::writeConstraint(
          //     fmt::format("(= M_m1r{}c{}_m1r{}c{} false)", 5, col, 6, col));
          if (!SMTCell::ifAssigned(middle_metal)) {
            SMTCell::setVar(middle_metal, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(
                fmt::format(" (= {} false) ", middle_metal));
          }
          // [10/04/2024] LISD FLAG: avoid duplicated via connections
          SMTCell::writeConstraint("(and");
          // SMTCell::writeConstraint(
          //     fmt::format(" ((_ at-most 1) (= M_m1r{}c{}_m2r{}c{} true) (= "
          //                 "M_m1r{}c{}_m2r{}c{} true))",
          //                 4, col, 4, col, 5, col, 5, col));
          // if lisd is not true, pmos can only connect to the one top via
          std::string first_via =
              fmt::format("M_m1r{}c{}_m2r{}c{}", 4, col, 4, col);
          std::string second_via =
              fmt::format("M_m1r{}c{}_m2r{}c{}", 5, col, 5, col);
          SMTCell::writeConstraint(fmt::format(" ((_ at-most 1)"));
          if (!SMTCell::ifAssigned(first_via)) {
            SMTCell::setVar(first_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", first_via));
          }
          if (!SMTCell::ifAssigned(second_via)) {
            SMTCell::setVar(second_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", second_via));
          }
          SMTCell::writeConstraint(")");
          // SMTCell::writeConstraint(
          //     fmt::format(" ((_ at-most 1) (= M_m1r{}c{}_m2r{}c{} true) (= "
          //                 "M_m1r{}c{}_m2r{}c{} true))",
          //                 6, col, 6, col, 7, col, 7, col));
          // if lisd is not true, nmos can only connect to the one bottom via
          first_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 6, col, 6, col);
          second_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 7, col, 7, col);
          SMTCell::writeConstraint(fmt::format(" ((_ at-most 1)"));
          if (!SMTCell::ifAssigned(first_via)) {
            SMTCell::setVar(first_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", first_via));
          }
          if (!SMTCell::ifAssigned(second_via)) {
            SMTCell::setVar(second_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", second_via));
          }
          SMTCell::writeConstraint(")");
          // [08/07/2024] LISD FLAG: avoid via sitting too close
          // SMTCell::writeConstraint(
          //     fmt::format(" ((_ at-most 1) (= M_m1r{}c{}_m2r{}c{} true) (= "
          //                 "M_m1r{}c{}_m2r{}c{} true))",
          //                 5, col, 5, col, 6, col, 6, col));
          first_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 5, col, 5, col);
          second_via = fmt::format("M_m1r{}c{}_m2r{}c{}", 6, col, 6, col);
          SMTCell::writeConstraint(fmt::format(" ((_ at-most 1)"));
          if (!SMTCell::ifAssigned(first_via)) {
            SMTCell::setVar(first_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", first_via));
          }
          if (!SMTCell::ifAssigned(second_via)) {
            SMTCell::setVar(second_via, 2);
            SMTCell::cnt("l", 3);
            SMTCell::writeConstraint(fmt::format(" (= {} true)", second_via));
          }
          SMTCell::writeConstraint(")");
        }
        SMTCell::writeConstraint("))");
        SMTCell::writeConstraint(")");
      } else if (SMTCell::getNumTrack() == 5) {
        fmt::print("ERROR: 5 Track is not supported yet\n");
        exit(1);
      } else {
        SMTCell::writeConstraint(fmt::format(" (= 1 1))\n"));
      }
      SMTCell::writeConstraint(fmt::format(")\n"));
    }
  }
}

void Placement::write_lisd_col_has_pin_alignment_or_empty_space() {
  /*
  This method also returns the list of columns that could be used for LISD
  */
  SMTCell::clear_lisd_col(); // clear the lisd columns
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(fmt::format(
        ";[SITE {}] Set LISD connection with pin alignment (1) two pins are "
        "aligned (2) a pin column has nothing on the other side\n",
        site_idx));
    // record the lisd columns using a vector
    int metal = 1;
    /*Disregard last col for now*/
    // for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) -
    // 2;
    //      col_idx++) {
    for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
      if (!SMTCell::ifSDCol_AGR(metal, col)) {
        continue;
      }
      // use tuple to store the net and the commodity
      std::vector<std::tuple<std::string, std::string>> tmp_pmos_commodity;
      std::vector<std::tuple<std::string, std::string>> tmp_nmos_commodity;
      std::vector<std::tuple<std::string, std::string>>
          tmp_source_sink_commodity;
      std::vector<std::tuple<int, int>> tmp_source_sink_inst;
      std::vector<std::tuple<std::string, std::string>> tmp_sink_sink_commodity;
      std::vector<std::tuple<int, int>> tmp_sink_sink_inst;
      // for each net, gather pmos and nmos pin
      for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
        bool is_source_valid = false;
        // for each source
        std::string pin_idx_source =
            SMTCell::getNet(netIndex)->getSource_ofNet();
        std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
        int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
        // for each sink
        for (int commodityIndex = 0;
             commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex++) {
          bool is_sink_valid = false;
          std::string pin_idx_sink =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
          std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
          int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
          if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
            continue;
          }
          if (source_pin->getInstID() == "ext" ||
              sink_pin->getInstID() == "ext") {
            continue;
          }
          // ## Skip If Source/Sink TR is in the same region
          if ((source_inst_idx <= SMTCell::getLastIdxPMOS() &&
               sink_inst_idx <= SMTCell::getLastIdxPMOS()) ||
              (source_inst_idx > SMTCell::getLastIdxPMOS() &&
               sink_inst_idx > SMTCell::getLastIdxPMOS())) {
            continue;
          }

          int row_source;
          int row_sink;
          row_source = SMTCell::get_mos_pin_row_by_site_idx(
              site_idx, SMTCell::ifInstPMOS(source_inst_idx));
          row_sink = SMTCell::get_mos_pin_row_by_site_idx(
              site_idx, SMTCell::ifInstPMOS(sink_inst_idx));
          // construct the variable name
          Triplet vCoord_source = Triplet(metal, row_source, col);
          Triplet vCoord_sink = Triplet(metal, row_sink, col);
          std::string tmp_str_source = "";
          std::string tmp_str_sink = "";
          tmp_str_source = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord_source.getVName(), pin_idx_source);
          tmp_str_sink = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord_sink.getVName(), pin_idx_sink);
          // source pin must not be gate
          if (source_pin->getPinType() == Pin::SOURCE ||
              source_pin->getPinType() == Pin::DRAIN) {
            is_source_valid = true;
          }
          if (!SMTCell::ifAssigned(tmp_str_source) && is_source_valid) {
            if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
              tmp_pmos_commodity.push_back(
                  std::make_tuple(tmp_str_source, pin_idx_source));
            } else {
              tmp_nmos_commodity.push_back(
                  std::make_tuple(tmp_str_source, pin_idx_source));
            }
          }
          // sink pin must not be gate
          if (sink_pin->getPinType() == Pin::SOURCE ||
              sink_pin->getPinType() == Pin::DRAIN) {
            is_sink_valid = true;
          }
          if (!SMTCell::ifAssigned(tmp_str_sink) && is_sink_valid) {
            if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
              tmp_pmos_commodity.push_back(
                  std::make_tuple(tmp_str_sink, pin_idx_sink));
            } else {
              tmp_nmos_commodity.push_back(
                  std::make_tuple(tmp_str_sink, pin_idx_sink));
            }
          }
        }
      }
      // between source and sink instances
      for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
        // for each source with each sink
        std::string pin_idx_source =
            SMTCell::getNet(netIndex)->getSource_ofNet();
        std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
        int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
        for (int commodityIndex = 0;
             commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex++) {
          std::string tmp_vname = "";
          // inst pin idx
          std::string pin_idx_sink =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
          // external net should NOT be considered
          if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
            continue;
          }
          // ignore startIdx and endIdx, not used
          std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
          int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
          // fmt::print("FLAG # 1 netIndex {} commodityIndex: {}\n", netIndex,
          // commodityIndex); external net should NOT be considered
          if (source_pin->getInstID() == "ext" ||
              sink_pin->getInstID() == "ext") {
            continue;
          }
          // ## Skip If Source/Sink TR is in the same region
          if ((source_inst_idx <= SMTCell::getLastIdxPMOS() &&
               sink_inst_idx <= SMTCell::getLastIdxPMOS()) ||
              (source_inst_idx > SMTCell::getLastIdxPMOS() &&
               sink_inst_idx > SMTCell::getLastIdxPMOS())) {
            continue;
          }
          int row_source;
          int row_sink;
          row_source = SMTCell::get_mos_pin_row_by_site_idx(
              site_idx, SMTCell::ifInstPMOS(source_inst_idx));
          row_sink = SMTCell::get_mos_pin_row_by_site_idx(
              site_idx, SMTCell::ifInstPMOS(sink_inst_idx));
          // ## Skip if either Source/Sink Pin is "Gate" Pin
          if (source_pin->getPinType() == Pin::GATE ||
              sink_pin->getPinType() == Pin::GATE) {
            continue;
          }

          Triplet vCoord_source = Triplet(metal, row_source, col);
          Triplet vCoord_sink = Triplet(metal, row_sink, col);
          std::string tmp_str_source = "";
          std::string tmp_str_sink = "";
          tmp_str_source = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord_source.getVName(), pin_idx_source);
          tmp_str_sink = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord_sink.getVName(), pin_idx_sink);
          // fmt::print("tmp_str_s: {}   tmp_str_t: {}\n", tmp_str_source,
          // tmp_str_sink);
          if (!SMTCell::ifAssigned(tmp_str_source) &&
              !SMTCell::ifAssigned(tmp_str_sink)) {
            SMTCell::setVar(tmp_str_source, 2);
            SMTCell::cnt("l", 3);
            SMTCell::setVar(tmp_str_sink, 2);
            SMTCell::cnt("l", 3);
            tmp_source_sink_commodity.push_back(
                std::make_tuple(tmp_str_source, tmp_str_sink));
            tmp_source_sink_inst.push_back(
                std::make_tuple(source_inst_idx, sink_inst_idx));
          }
        }
      } // end of for loop for each net
      // between sink instances
      for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
        for (int commodityIndex_1 = 0;
             commodityIndex_1 < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex_1++) {

          for (int commodityIndex_2 = commodityIndex_1;
               commodityIndex_2 < SMTCell::getNet(netIndex)->getNumSinks();
               commodityIndex_2++) {
            // inst pin idx
            std::string pin_idx_sink_1 =
                SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex_1);
            std::string pin_idx_sink_2 =
                SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex_2);
            // external net should NOT be considered
            if (pin_idx_sink_1 == Pin::keySON ||
                pin_idx_sink_2 == Pin::keySON) {
              continue;
            }
            // ignore startIdx and endIdx, not used
            std::shared_ptr<Pin> sink_pin_1 = SMTCell::getPin(pin_idx_sink_1);
            std::shared_ptr<Pin> sink_pin_2 = SMTCell::getPin(pin_idx_sink_2);
            // external net should NOT be considered
            if (sink_pin_1->getInstID() == "ext" ||
                sink_pin_2->getInstID() == "ext") {
              continue;
            }
            int sink_inst_1_idx = SMTCell::getPinInstIdx(sink_pin_1);
            int sink_inst_2_idx = SMTCell::getPinInstIdx(sink_pin_2);
            // ## Skip If Source/Sink TR is in the same region
            if ((sink_inst_1_idx <= SMTCell::getLastIdxPMOS() &&
                 sink_inst_2_idx <= SMTCell::getLastIdxPMOS()) ||
                (sink_inst_1_idx > SMTCell::getLastIdxPMOS() &&
                 sink_inst_2_idx > SMTCell::getLastIdxPMOS())) {
              continue;
            }

            int row_sink_1;
            int row_sink_2;
            row_sink_1 = SMTCell::get_mos_pin_row_by_site_idx(
                site_idx, SMTCell::ifInstPMOS(sink_inst_1_idx));
            row_sink_2 = SMTCell::get_mos_pin_row_by_site_idx(
                site_idx, SMTCell::ifInstPMOS(sink_inst_2_idx));

            // ## Skip if either Source/Sink Pin is "Gate" Pin
            if (sink_pin_1->getPinType() == Pin::GATE ||
                sink_pin_2->getPinType() == Pin::GATE) {
              continue;
            }
            Triplet vCoord_sink_1 = Triplet(metal, row_sink_1, col);
            Triplet vCoord_sink_2 = Triplet(metal, row_sink_2, col);

            std::string tmp_str_sink_1 = "";
            std::string tmp_str_sink_2 = "";

            tmp_str_sink_1 = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex_1, vCoord_sink_1.getVName(), pin_idx_sink_1);
            tmp_str_sink_2 = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex_2, vCoord_sink_2.getVName(), pin_idx_sink_2);

            if (!SMTCell::ifAssigned(tmp_str_sink_1) &&
                !SMTCell::ifAssigned(tmp_str_sink_2)) {
              SMTCell::setVar(tmp_str_sink_1, 2);
              SMTCell::cnt("l", 3);
              SMTCell::setVar(tmp_str_sink_2, 2);
              SMTCell::cnt("l", 3);
              tmp_sink_sink_commodity.push_back(
                  std::make_tuple(tmp_str_sink_1, tmp_str_sink_2));
              tmp_sink_sink_inst.push_back(
                  std::make_tuple(sink_inst_1_idx, sink_inst_2_idx));
            }
          }
        }
      }
      // if no variable is assigned, skip the constraint
      if (tmp_source_sink_commodity.size() == 0 &&
          tmp_sink_sink_commodity.size() == 0 &&
          tmp_pmos_commodity.size() == 0 && tmp_nmos_commodity.size() == 0) {
        continue;
      }
      // set lisd column
      SMTCell::set_lisd_col(site_idx, col);
      SMTCell::writeConstraint(
          fmt::format("(assert (ite (= lisd_s{}m1c{} true) ", site_idx, col));
      // SMTCell::writeConstraint("(or ");
      bool is_case_1_written = false;
      // Case 1: pin alignment between (source and sink) or (sink and sink)
      if (tmp_source_sink_commodity.size() != 0 ||
          tmp_sink_sink_commodity.size() != 0) {
        SMTCell::writeConstraint(
            fmt::format("((_ at-least 1) ")); // [09/25/2024] must have pin to
                                              // make lisd true
        is_case_1_written = true;
      }
      if (tmp_source_sink_commodity.size() != 0) {
        for (size_t i = 0; i < tmp_source_sink_commodity.size(); i++) {
          SMTCell::writeConstraint(
              fmt::format("(and (= {} true) (= {} true)) ",
                          std::get<0>(tmp_source_sink_commodity[i]),
                          std::get<1>(tmp_source_sink_commodity[i])));
        }
      }
      if (tmp_sink_sink_commodity.size() != 0) {
        for (size_t i = 0; i < tmp_sink_sink_commodity.size(); i++) {
          SMTCell::writeConstraint(
              fmt::format("(and (= {} true) (= {} true)) ",
                          std::get<0>(tmp_sink_sink_commodity[i]),
                          std::get<1>(tmp_sink_sink_commodity[i])));
        }
      }
      if (is_case_1_written) {
        SMTCell::writeConstraint(") ");
      }
      // Case 2 - ignored for multi-height
      // SMTCell::writeConstraint(")");
      // SMTCell::writeConstraint(
      //     fmt::format(" (= lisd_s{}m1c{} false)))\n", site_idx, col));
      if (tmp_source_sink_commodity.size() != 0 ||
          tmp_sink_sink_commodity.size() != 0) {
        SMTCell::writeConstraint(fmt::format("(and")); // [09/25/2024] must have
                                                       // pin to make lisd true
        is_case_1_written = true;
      }
      if (tmp_source_sink_commodity.size() != 0) {
        for (size_t i = 0; i < tmp_source_sink_commodity.size(); i++) {
          SMTCell::writeConstraint(
              fmt::format(" (not (and (= {} true) (= {} true)))",
                          std::get<0>(tmp_source_sink_commodity[i]),
                          std::get<1>(tmp_source_sink_commodity[i])));
        }
      }
      if (tmp_sink_sink_commodity.size() != 0) {
        for (size_t i = 0; i < tmp_sink_sink_commodity.size(); i++) {
          SMTCell::writeConstraint(
              fmt::format(" (not (and (= {} true) (= {} true)))",
                          std::get<0>(tmp_sink_sink_commodity[i]),
                          std::get<1>(tmp_sink_sink_commodity[i])));
        }
      }

      if (is_case_1_written) {
        SMTCell::writeConstraint(")");
      }
      SMTCell::writeConstraint("))\n");
      // else, either [row 0 and row 2] or [row 1 and row 3] or [row 1] or [row
      // 3] or [row 0] or [row 2] or nothing
    } // end of for loop for each column
  }
}

void Placement::write_max_func(FILE *fp) {
  fmt::print(
      fp,
      "(define-fun max ((x (_ BitVec {})) (y (_ BitVec {}))) (_ BitVec {})\n",
      SMTCell::getBitLength_numTrackV(), SMTCell::getBitLength_numTrackV(),
      SMTCell::getBitLength_numTrackV());
  fmt::print(fp, "  (ite (bvsgt x y) x y)\n");
  fmt::print(fp, ")\n");
}

void Placement::write_placement_var(FILE *fp) {
  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    // instance x position
    fmt::print(fp, "(declare-const x{} (_ BitVec {}))\n", i,
               SMTCell::getBitLength_numTrackV());
    SMTCell::cnt("v", 0);
    // instance flip flag
    fmt::print(fp, "(declare-const ff{} Bool)\n", i);
    SMTCell::cnt("v", 0);
    // instance y position
    fmt::print(fp, "(declare-const y{} (_ BitVec {}))\n", i,
               SMTCell::getBitLength_numPTrackH());
    // unit width
    fmt::print(fp, "(declare-const uw{} (_ BitVec {}))\n", i,
               SMTCell::getBitLength_trackEachPRow());
    // width
    fmt::print(fp, "(declare-const w{} (_ BitVec {}))\n", i,
               (bmp::msb(2 * tmp_finger[0] + 1) + 1));
    // num of finger
    fmt::print(fp, "(declare-const nf{} (_ BitVec {}))\n", i,
               (bmp::msb(tmp_finger[0]) + 1));
  }
}

void Placement::write_placement_range_constr(FILE *fp) {
  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    int len = SMTCell::getBitLength_numTrackV();
    // WARN FLAG: Ignore intermediate steps. Not used at all
    fmt::print(
        fp, "(assert (and (bvsge x{} (_ bv{} {})) (bvsle x{} (_ bv{} {}))))\n",
        i, SMTCell::getOffset(1), len, i,
        std::to_string(SMTCell::getNumTrackV() - (2 * tmp_finger[0] + 1)), len);
    SMTCell::cnt("l", 0);
    SMTCell::cnt("l", 0);
    SMTCell::cnt("c", 0);
  }
}

void Placement::set_placement_var_pmos(FILE *fp) {
  for (int i = 0; i < SMTCell::getLastIdxPMOS() + 1; i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());

    fmt::print(fp, "(assert (or ");
    for (auto placeable_row_it = SMTCell::pmos_placeable_rows_begin();
         placeable_row_it != SMTCell::pmos_placeable_rows_end();
         placeable_row_it++) {
      int placeable_row = *placeable_row_it;
      fmt::print(fp, "(= y{} (_ bv{} {})) ", i, placeable_row,
                 SMTCell::getBitLength_numPTrackH());
    }
    fmt::print(fp, "))\n");

    fmt::print(fp, "(assert (= nf{} (_ bv{} {})))\n", i, tmp_finger[0],
               bmp::msb(tmp_finger[0]) + 1);

    fmt::print(fp, "(assert (= uw{} (_ bv{} {})))\n", i,
               SMTCell::getInst(i)->getInstWidth() / tmp_finger[0],
               SMTCell::getBitLength_trackEachPRow());

    fmt::print(fp, "(assert (= w{} (_ bv{} {})))\n", i, (2 * tmp_finger[0] + 1),
               bmp::msb(2 * tmp_finger[0] + 1) + 1);
  }

  fmt::print(fp, ";At least one PMOS on each row\n");
  for (auto placeable_row_it = SMTCell::pmos_placeable_rows_begin();
       placeable_row_it != SMTCell::pmos_placeable_rows_end();
       placeable_row_it++) {
    fmt::print(fp, "(assert (or ");
    for (int i = 0; i < SMTCell::getLastIdxPMOS() + 1; i++) {
      fmt::print(fp, "(= y{} (_ bv{} {})) ", i, *placeable_row_it,
                 SMTCell::getBitLength_numPTrackH());
    }
    fmt::print(fp, "))\n");
  }
}

void Placement::set_placement_var_nmos(FILE *fp) {
  for (int i = SMTCell::getLastIdxPMOS() + 1; i < SMTCell::getInstCnt(); i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());

    fmt::print(fp, "(assert (or ");
    for (auto placeable_row_it = SMTCell::nmos_placeable_rows_begin();
         placeable_row_it != SMTCell::nmos_placeable_rows_end();
         placeable_row_it++) {
      int placeable_row = *placeable_row_it;
      fmt::print(fp, "(= y{} (_ bv{} {})) ", i, placeable_row,
                 SMTCell::getBitLength_numPTrackH());
    }
    fmt::print(fp, "))\n");

    fmt::print(fp, "(assert (= nf{} (_ bv{} {})))\n", i, tmp_finger[0],
               bmp::msb(tmp_finger[0]) + 1);

    fmt::print(fp, "(assert (= uw{} (_ bv{} {})))\n", i,
               SMTCell::getInst(i)->getInstWidth() / tmp_finger[0],
               SMTCell::getBitLength_trackEachPRow());

    fmt::print(fp, "(assert (= w{} (_ bv{} {})))\n", i, (2 * tmp_finger[0] + 1),
               bmp::msb(2 * tmp_finger[0] + 1) + 1);
  }

  fmt::print(fp, ";At least one NMOS on each row\n");
  for (auto placeable_row_it = SMTCell::nmos_placeable_rows_begin();
       placeable_row_it != SMTCell::nmos_placeable_rows_end();
       placeable_row_it++) {
    fmt::print(fp, "(assert (or ");
    for (int i = SMTCell::getLastIdxPMOS() + 1; i < SMTCell::getInstCnt();
         i++) {
      fmt::print(fp, "(= y{} (_ bv{} {})) ", i, *placeable_row_it,
                 SMTCell::getBitLength_numPTrackH());
    }
    fmt::print(fp, "))\n");
  }
}

void Placement::write_XOL(FILE *fp, bool ifPMOS, int XOL_Mode,
                          int NDE_Parameter, int XOL_Parameter) {
  int startIdx = 0;
  int endIdx = 0;

  if (ifPMOS) {
    startIdx = 0;
    endIdx = SMTCell::getLastIdxPMOS() + 1;
  } else {
    startIdx = SMTCell::getLastIdxPMOS() + 1;
    endIdx = SMTCell::getInstCnt();
  }
  // convert from int to const size_t?
  // int i = 0;
  // const size_t j = i;

  // XOL Mode => 0: SDB, 1:DDB, 2:(Default)SDB/DDB mixed
  for (int i = startIdx; i < endIdx; i++) {
    // For instance i, retrieve pin IDs of source and drain
    int tmp_key_S_i =
        SMTCell::getInstWPinNetID(SMTCell::getInst(i)->getInstName() + "_S");
    int tmp_key_D_i =
        SMTCell::getInstWPinNetID(SMTCell::getInst(i)->getInstName() + "_D");
    std::vector<int> tmp_finger_i = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    int height_i = SMTCell::getInst(i)->getInstWidth() / tmp_finger_i[0];

    if (XOL_Mode > 0) {
      fmt::print(fp, "(declare-const fol_l_x{} Bool)\n", i);
      fmt::print(fp, "(declare-const fol_r_x{} Bool)\n", i);

      std::string tmp_str_xol_l = "(assert (ite (not (or";
      std::string tmp_str_xol_r = "(assert (ite (not (or";
      int cnt_xol = 0;

      for (int k = startIdx; k < endIdx; k++) {
        int len = SMTCell::getBitLength_numTrackV();
        // for every pair of PMOS
        if (k != i) {
          // For instance k, retrieve pin IDs of source and drain
          int tmp_key_S_k = SMTCell::getInstWPinNetID(
              SMTCell::getInst(k)->getInstName() + "_S");
          int tmp_key_D_k = SMTCell::getInstWPinNetID(
              SMTCell::getInst(k)->getInstName() + "_D");
          std::vector<int> tmp_finger_k = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(k)->getInstWidth(), SMTCell::getTrackEachPRow());
          int height_k = SMTCell::getInst(k)->getInstWidth() / tmp_finger_k[0];

          if (NDE_Parameter == 0 && height_i != height_k) {
            continue; // diffusion sharing with different height
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_k[0] % 2 == 0 &&
                     tmp_key_S_i != tmp_key_S_k) {
            continue;
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_k[0] % 2 == 1 &&
                     tmp_key_S_i != tmp_key_S_k && tmp_key_S_i != tmp_key_D_k) {
            continue;
          } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_k[0] % 2 == 0 &&
                     tmp_key_S_k != tmp_key_S_i && tmp_key_S_k != tmp_key_D_i) {
            continue;
          } else if (tmp_key_S_k != tmp_key_S_i && tmp_key_S_k != tmp_key_D_i &&
                     tmp_key_D_k != tmp_key_S_i && tmp_key_D_k != tmp_key_D_i) {
            continue;
          }
          // AGR FLAG : only scale by M1 Pitch since this is adding cell width
          fmt::print(fp,
                     "(assert (ite (= (bvadd x{} (_ bv{} {})) x{}) (= "
                     "fol_r_x{} true) (= #b1 #b1)))\n",
                     i, (2 * tmp_finger_i[0]), len, k, i);
          fmt::print(fp,
                     "(assert (ite (= (bvsub x{} (_ bv{} {})) x{}) (= "
                     "fol_l_x{} true) (= #b1 #b1)))\n",
                     i, (2 * tmp_finger_k[0]), len, k, i);
          tmp_str_xol_l += " (= (bvadd x" + std::to_string(i) + " (_ bv" +
                           std::to_string(2 * tmp_finger_i[0]) + " " +
                           std::to_string(len) + ")) x" + std::to_string(k) +
                           ")";
          tmp_str_xol_r += " (= (bvsub x" + std::to_string(i) + " (_ bv" +
                           std::to_string(2 * tmp_finger_k[0]) + " " +
                           std::to_string(len) + ")) x" + std::to_string(k) +
                           ")";
          cnt_xol++;
        }
      }
      tmp_str_xol_l +=
          ")) (= fol_r_x" + std::to_string(i) + " false) (= #b1 #b1)))\n";
      tmp_str_xol_r +=
          ")) (= fol_l_x" + std::to_string(i) + " false) (= #b1 #b1)))\n";

      if (cnt_xol > 0) {
        fmt::print(fp, "{}", tmp_str_xol_l);
        fmt::print(fp, "{}", tmp_str_xol_r);
      } else {
        fmt::print(fp, "(assert (= fol_r_x{} false))\n", i);
        fmt::print(fp, "(assert (= fol_l_x{} false))\n", i);
      }
    }

    for (int j = startIdx; j < endIdx; j++) {
      if (i != j) {
        // For instance i, retrieve pin IDs of source and drain
        int tmp_key_S_j = SMTCell::getInstWPinNetID(
            SMTCell::getInst(j)->getInstName() + "_S");
        int tmp_key_D_j = SMTCell::getInstWPinNetID(
            SMTCell::getInst(j)->getInstName() + "_D");
        std::vector<int> tmp_finger_j = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(j)->getInstWidth(), SMTCell::getTrackEachPRow());
        int height_j = SMTCell::getInst(j)->getInstWidth() / tmp_finger_j[0];

        int canShare = 1;
        if (NDE_Parameter == 0 && height_i != height_j) {
          canShare = 0;
        } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0 &&
                   tmp_key_S_i != tmp_key_S_j) {
          canShare = 0;
        } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1 &&
                   tmp_key_S_i != tmp_key_S_j && tmp_key_S_i != tmp_key_D_j) {
          canShare = 0;
        } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0 &&
                   tmp_key_S_j != tmp_key_S_i && tmp_key_S_j != tmp_key_D_i) {
          canShare = 0;
        } else if (tmp_key_S_j != tmp_key_S_i && tmp_key_S_j != tmp_key_D_i &&
                   tmp_key_D_j != tmp_key_S_i && tmp_key_D_j != tmp_key_D_i) {
          canShare = 0;
        }

        std::string tmp_str_ij;
        std::string tmp_str_ji;

        if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0) {
          tmp_str_ij = "(= (_ bv" + std::to_string(tmp_key_S_i) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       ") (_ bv" + std::to_string(tmp_key_S_j) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       "))";
          tmp_str_ji = "(= (_ bv" + std::to_string(tmp_key_S_i) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       ") (_ bv" + std::to_string(tmp_key_S_j) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       "))";
        } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1) {
          // # if nf % 2 == 1, if ff = 1 nl = $tmp_key_D, nr = $tmp_key_S
          // #                 if ff = 0 nl = $tmp_key_S, nr = $tmp_key_D
          // # nri = nlj
          if (tmp_key_S_i == tmp_key_D_j) {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ij.clear();
            } else {
              tmp_str_ij = "(= ff" + std::to_string(j) + " true)";
            }
          } else {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ij = "(= ff" + std::to_string(j) + " false)";
            } else {
              tmp_str_ij = "(= #b0 #b1)";
            }
          }
          // # nli = nrj
          if (tmp_key_S_i == tmp_key_S_j) {
            if (tmp_key_S_i == tmp_key_D_j) {
              tmp_str_ji.clear();
            } else {
              tmp_str_ji = "(= ff" + std::to_string(j) + " true)";
            }
          } else {
            if (tmp_key_S_i == tmp_key_D_j) {
              tmp_str_ji = "(= ff" + std::to_string(j) + " false)";
            } else {
              tmp_str_ji = "(= #b0 #b1)";
            }
          }
        } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0) {
          // # if nf % 2 == 1, if ff = 1 nl = $tmp_key_D, nr = $tmp_key_S
          // #                 if ff = 0 nl = $tmp_key_S, nr = $tmp_key_D
          // # nri = nlj
          if (tmp_key_S_i == tmp_key_S_j) {
            if (tmp_key_D_i == tmp_key_S_j) {
              tmp_str_ij.clear();
            } else {
              tmp_str_ij = "(= ff" + std::to_string(i) + " true)";
            }
          } else {
            if (tmp_key_D_i == tmp_key_S_j) {
              tmp_str_ij = "(= ff" + std::to_string(i) + " false)";
            } else {
              tmp_str_ij = "(= #b0 #b1)";
            }
          }
          // # nli = nrj
          if (tmp_key_D_i == tmp_key_S_j) {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ji.clear();
            } else {
              tmp_str_ji = "(= ff" + std::to_string(i) + " true)";
            }
          } else {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ji = "(= ff" + std::to_string(i) + " false)";
            } else {
              tmp_str_ji = "(= #b0 #b1)";
            }
          }
        } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 1) {
          // # if nf % 2 == 1, if ff = 1 nl = $tmp_key_D, nr = $tmp_key_S
          // #                 if ff = 0 nl = $tmp_key_S, nr = $tmp_key_D
          // # nri = nlj
          if (tmp_key_S_i == tmp_key_D_j) {
            if (tmp_key_S_i == tmp_key_S_j) {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi = 0,1, ffj = 0,1
                  tmp_str_ij.clear();
                } else {
                  // ## ffi,ffj!=0 at the same time
                  tmp_str_ij = "(or (>= ff" + std::to_string(i) +
                               " true) (>= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ~(ffi=0 & ffj=1)
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi = 1
                  tmp_str_ij = "(= ff" + std::to_string(i) + " true)";
                }
              }
            } else {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffj=1 or (ffi = 0 and ffj= 0)
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " false)) (= ff" + std::to_string(j) + " true))";
                } else {
                  // ## ffj=1
                  tmp_str_ij = "(= ff" + std::to_string(j) + " true)";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi = ffj
                  tmp_str_ij = "(= ff" + std::to_string(i) + " ff" +
                               std::to_string(j) + ")";
                } else {
                  // ## ffi=1 and ffj=1
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " true))";
                }
              }
            }
          } else {
            if (tmp_key_S_i == tmp_key_S_j) {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## (ffi=0 and ffj=1) or ffj=0
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## (ffi=0 and ffj=1) or (ffi=1 and ffj=0)
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false)))";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffj =0
                  tmp_str_ij = "(= ff" + std::to_string(j) + " false)";
                } else {
                  // ## ffi=1 and ffj=0
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false))";
                }
              }
            } else {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi=0
                  tmp_str_ij = "(= ff" + std::to_string(j) + " false)";
                } else {
                  // ## ffi=0 and ffj=1
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi=0 and ffj=0
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi=0 and ffj=0
                  tmp_str_ij = "(= #b1 #b0)";
                }
              }
            }
          }

          // # nli = nrj
          if (tmp_key_D_i == tmp_key_S_j) {
            if (tmp_key_D_i == tmp_key_D_j) {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi = 0,1, ffj = 0,1
                  tmp_str_ji.clear();
                } else {
                  // ## ffi,ffj!=0 at the same time
                  tmp_str_ji = "(or (>= ff" + std::to_string(i) +
                               " true) (>= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ~(ffi=0 & ffj=1)
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi = 1
                  tmp_str_ji = "(= ff" + std::to_string(i) + " true)";
                }
              }
            } else {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffj=1 or (ffi = 0 and ffj= 0)
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " false)) (= ff" + std::to_string(j) + " true))";
                } else {
                  // ## ffj=1
                  tmp_str_ji = "(= ff" + std::to_string(j) + " true)";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi = ffj
                  tmp_str_ji = "(= ff" + std::to_string(i) + " ff" +
                               std::to_string(j) + ")";
                } else {
                  // ## ffi=1 and ffj=1
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " true))";
                }
              }
            }
          } else {
            if (tmp_key_D_i == tmp_key_D_j) {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## (ffi=0 and ffj=1) or ffj=0
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## (ffi=0 and ffj=1) or (ffi=1 and ffj=0)
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false)))";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffj =0
                  tmp_str_ji = "(= ff" + std::to_string(i) + " false)";
                } else {
                  // ## ffi=1 and ffj=0
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false))";
                }
              }
            } else {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi=0
                  tmp_str_ji = "(= ff" + std::to_string(j) + " false)";
                } else {
                  // ## ffi=0 and ffj=1
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi=0 and ffj=0
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi=0 and ffj=0
                  tmp_str_ji = "(= #b1 #b0)";
                }
              }
            }
          }
        }

        // AGR FLAG : only scale up by M1 pitch since adding cell width
        int len = SMTCell::getBitLength_numTrackV();
        std::string f_wi = "(_ bv" + std::to_string(2 * tmp_finger_i[0]) + " " +
                           std::to_string(len) + ")";
        std::string f_wj = "(_ bv" + std::to_string(2 * tmp_finger_j[0]) + " " +
                           std::to_string(len) + ")";
        std::string xol = "(_ bv" + std::to_string(XOL_Parameter) + " " +
                          std::to_string(len) + ")";
        std::string xol_i =
            "(_ bv" + std::to_string((2 * tmp_finger_i[0] + XOL_Parameter)) +
            " " + std::to_string(len) + ")";
        std::string xol_j =
            "(_ bv" + std::to_string((2 * tmp_finger_j[0] + XOL_Parameter)) +
            " " + std::to_string(len) + ")";
        std::string xol_i_o =
            "(_ bv" +
            std::to_string((2 * tmp_finger_i[0] + XOL_Parameter - 2)) + " " +
            std::to_string(len) + ")";
        std::string xol_j_o =
            "(_ bv" +
            std::to_string((2 * tmp_finger_j[0] + XOL_Parameter - 2)) + " " +
            std::to_string(len) + ")";

        int tmp_idx = 0;

        if (ifPMOS) {
          tmp_idx = SMTCell::getLastIdxPMOS();
        } else {
          if (NDE_Parameter == 1) {
            height_i = height_j;
          }
          tmp_idx =
              SMTCell::getNumInstance() - 1 - SMTCell::getLastIdxPMOS() - 1;
        }

        if (XOL_Mode > 0 && tmp_idx >= 2) {
          fmt::print(fp,
                     "(assert (ite (= y{} y{}) (ite (and fol_r_x{} (bvslt "
                     "(bvadd x{} {}) x{})) "
                     "(bvsle (bvadd x{} {}) x{})\n",
                     i, j, i, i, f_wi, j, i, xol_i_o, j);

          if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0) {
            // # sourses of both inst are the same => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i_o, j);
            }
            // # sources of both inst are different => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1) {
            // # source of inst i is same as source and drain of inst j => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_S_j && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, i, i, xol_i_o, j);
            }
            // # source of inst i is same as source of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i is same as drain of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0) {
            // # source of inst j is same as source and drain of inst i => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_j == tmp_key_S_i && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i_o);
            }

            // # source of inst j is same as source of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # source of inst j is same as drain of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          } else {
            // fmt::print("\n\t FLAG 1 outer {}, {}, {}\t\n", tmp_key_D_i,
            //            tmp_key_D_j,
            //            (XOL_Mode == 2 &&
            //             (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
            //             tmp_key_D_i == tmp_key_D_j));
            // if (!(XOL_Mode == 2 &&
            //             (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
            //             tmp_key_D_i == tmp_key_D_j)) {
            //   fmt::print("\n\t FLAG 1 inner {}, {}, {}\t\n", (XOL_Mode == 2),
            //              (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)),
            //              (tmp_key_D_i == tmp_key_D_j));
            // }
            // # all source/drain are the same ==> SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_D_i && tmp_key_S_j == tmp_key_D_j &&
                tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i_o, j);
            }
            // # source/drain of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # source/drain of inst i && drain of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # source/drain of inst j && source of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # source/drain of inst j && drain of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # source of inst i && source of inst j, drain of inst i && drain
            // of inst j are the same => conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j && tmp_key_D_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (or (and (not ff{}) ff{}) (and ff{} "
                         "(not ff{}))) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i && drain of inst j, drain of inst i && source
            // of inst j are the same => coinditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j && tmp_key_D_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (or (and (not ff{}) (not ff{})) (and "
                         "ff{} ff{})) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (and ff{} (not ff{})) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (and ff{} ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // # drain of inst i && source of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_S_j) {
              fmt::print(
                  fp,
                  "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle (bvadd "
                  "x{} (ite (and (not ff{}) (not ff{})) {} {})) x{})\n",
                  i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // # drain of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_D_j) {
              // fmt::print("\n\t FLAG 1 \t\n");
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (and (not ff{}) ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          }

          if (canShare == 1) {
            fmt::print(fp,
                       "		(ite (and (= (bvadd x{} {}) x{}) {}) "
                       "(= (bvadd x{} {}) x{})\n",
                       i, f_wi, j, tmp_str_ij, i, f_wi, j);
          }

          fmt::print(fp,
                     "		(ite (and fol_l_x{} (bvsgt (bvsub x{} {}) "
                     "x{})) (bvsge (bvsub x{} {}) x{})\n",
                     i, i, f_wj, j, i, xol_j_o, j);
          if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0) {
            // # sourses of both inst are the same => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                (tmp_key_S_i == tmp_key_S_j)) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # sources of both inst are different => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1) {
            // # source of inst i is same as source and drain of inst j => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_S_j && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # source of inst i is same as source of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i is same as drain of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0) {
            // # source of inst j is same as source and drain of inst i => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_j == tmp_key_S_i && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # source of inst j is same as source of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # source of inst j is same as drain of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          } else {
            // fmt::print("\n\t FLAG 2 outer {}, {}, {}\t\n", tmp_key_S_i,
            //            tmp_key_S_j,
            //            (XOL_Mode == 2 &&
            //             (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
            //             tmp_key_S_i == tmp_key_S_j));
            // if (!(XOL_Mode == 2 &&
            //      (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
            //      tmp_key_S_i == tmp_key_S_j)) {
            //   fmt::print("\n\t FLAG 2 inner {}, {}, {}\t\n", (XOL_Mode == 2),
            //              (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)),
            //              (tmp_key_S_i == tmp_key_S_j));
            // }

            // # all source/drain are the same ==> SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_D_i && tmp_key_S_j == tmp_key_D_j &&
                tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # source/drain of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # source/drain of inst i && drain of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # source/drain of inst j && source of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # source/drain of inst j && drain of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # source of inst i && source of inst j, drain of inst i && drain
            // of inst j are the same => conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j && tmp_key_D_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (or (and (not ff{}) ff{}) (and ff{} "
                         "(not ff{}))) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i && drain of inst j, drain of inst i && source
            // of inst j are the same => coinditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j && tmp_key_D_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (or (and (not ff{}) (not ff{})) (and "
                         "ff{} ff{})) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              // fmt::print("\n\t FLAG 2 \t\n");
              fmt::print(
                  fp,
                  "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                  "x{} (ite (and (not ff{}) ff{}) {} {})) x{})\n",
                  i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(
                  fp,
                  "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                  "x{} (ite (and (not ff{}) (not ff{})) {} {})) x{})\n",
                  i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # drain of inst i && source of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (and ff{} ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # drain of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (and ff{} (not ff{})) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          }

          if (canShare == 1) {
            fmt::print(fp,
                       "		(ite (and (= (bvsub x{} {}) x{}) {}) "
                       "(= (bvsub x{} {}) x{})\n",
                       i, f_wj, j, tmp_str_ji, i, f_wj, j);
          }

          if (canShare == 1) {
            fmt::print(fp, "		(= #b1 #b0))))))) (= 1 1)))\n");
          } else {
            fmt::print(fp, "		(= #b1 #b0))))) (= 1 1)))\n");
          }

        } else {
          if (canShare == 1) {

            fmt::print(fp,
                       "(assert (ite (= y{} y{}) (ite (bvslt (bvadd x{} {}) "
                       "x{}) (bvsle (bvadd "
                       "x{} {}) x{})\n",
                       i, j, i, f_wi, j, i, xol_i, j);
            fmt::print(fp,
                       "        (ite (and (= (bvadd x{} {}) x{}) {}) (= (bvadd "
                       "x{} {}) x{})\n",
                       i, f_wi, j, tmp_str_ij, i, f_wi, j);
            fmt::print(fp,
                       "        (ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                       "x{} {}) x{})\n",
                       i, f_wj, j, i, xol_j, j);
            fmt::print(fp,
                       "        (ite (and (= (bvsub x{} {}) x{}) {}) (= (bvsub "
                       "x{} {}) x{})\n",
                       i, f_wj, j, tmp_str_ji, i, f_wj, j);
            fmt::print(fp, "        (= #b1 #b0))))) (= 1 1)))\n");
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("c", 0);

          } else {

            fmt::print(fp,
                       "(assert (ite (= y{} y{}) (ite (bvslt (bvadd x{} {}) "
                       "x{}) (bvsle (bvadd "
                       "x{} {}) x{})\n",
                       i, j, i, f_wi, j, i, xol_i, j);
            fmt::print(fp,
                       "        (ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                       "x{} {}) x{})\n",
                       i, f_wj, j, i, xol_j, j);
            fmt::print(fp, "        (= #b1 #b0))) (= 1 1)))\n");
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("c", 0);
          }
        }
      }
    }
  }
}

void Placement::set_placement_legal_col(FILE *fp) {
  // int len = SMTCell::getBitLength_numTrackV();
  // define M1 constants
  // fmt::print(fp, "(declare-const m1Offset (_ BitVec {}))\n", len);
  // fmt::print(fp, "(declare-const m1EvenCol (_ BitVec {}))\n", len);
  // fmt::print(fp, "(declare-const m1MP (_ BitVec {}))\n", len);
  // fmt::print(fp, "(assert (= m1Offset (_ bv{} {})))\n",
  // SMTCell::getOffset(1),
  //            len);
  // fmt::print(fp, "(assert (= m1EvenCol (_ bv{} {})))\n",
  //            2 * SMTCell::getMetalPitch(1), len);
  // fmt::print(fp, "(assert (= m1MP (_ bv{} {})))\n",
  // SMTCell::getMetalPitch(1),
  //            len);
  // Any legal instance placement should land on an odd column
  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    // fmt::print(
    //     fp, "(assert (= (bvsmod (bvsub x{} m1Offset) m1EvenCol) m1MP))\n",
    //     i);
    fmt::print(fp, "(assert (= ((_ extract 0 0) x{}) #b1))\n", i);
  }
}

void Placement::set_default_G_metal() {
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(
        fmt::format(";[SITE {}] Set Default Gate Metal according to the "
                    "capacity variables\n",
                    site_idx));
    std::map<const std::string, int> h_tmp;
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
             vEdgeIndex++) {
          // ignoring $virtualEdges[$vEdgeIndex][2] =~ /^pin/ since this is
          // always a pin name
          // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
          std::shared_ptr<VirtualEdge> tmp_ve =
              SMTCell::getVirtualEdge(vEdgeIndex);
          std::string sourcePin = SMTCell::getNet(netIndex)->getSource_ofNet();
          std::string sinkPin =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
          if (tmp_ve->getPinName() == sourcePin) {
            std::shared_ptr<Pin> pin_s = SMTCell::getPin(sourcePin);
            // external net should NOT be considered
            if (pin_s->getInstID() == "ext") {
              continue;
            }
            // instance index
            int instIdx = SMTCell::getPinInstIdx(pin_s);
            std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
                SMTCell::getInst(instIdx)->getInstWidth(),
                SMTCell::getTrackEachPRow());

            int height;
            // AGR FLAG: adapt to different track height
            if (SMTCell::getNumTrack() == 2) {
              height = 2;
            } else if (SMTCell::getNumTrack() == 3) {
              height = 3;
            } else if (SMTCell::getNumTrack() == 4) {
              height = 3;
            } else if (SMTCell::getNumTrack() == 5 ||
                       SMTCell::getNumTrack() == 6) {
              height = 4;
            } else {
              fmt::print(stderr, "[ERROR] Unsupported track height\n");
              exit(1);
            }

            int metal = 1; // AGR FLAG: placement only considers M1

            // Source pin is Gate
            if (SMTCell::getPin(sourcePin)->getPinType() == Pin::GATE) {
              // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
              int tmp_col = tmp_ve->getVCoord()->col_;
              if (SMTCell::ifGCol_AGR(metal, tmp_col)) {
                // use copy constructor
                Triplet *tmp_vname_first = new Triplet(*tmp_ve->getVCoord());
                Triplet *tmp_vname_second = new Triplet(*tmp_ve->getVCoord());
                // PMOS
                if (instIdx <= SMTCell::getLastIdxPMOS()) {
                  for (int i = 0; i <= height - 2; i++) {
                    int j = i;
                    int k = j + 1;
                    tmp_vname_first->setRow(
                        SMTCell::
                            get_routing_row_by_site_idx_and_metal_and_row_idx(
                                site_idx, metal, j));
                    tmp_vname_second->setRow(
                        SMTCell::
                            get_routing_row_by_site_idx_and_metal_and_row_idx(
                                site_idx, metal, k));
                    // GC FLAG: check if gc is enabled or not before setting any
                    // gate variables GC FLAG: never need to cut gate 0
                    int FLAG_GATE_CUT = 0;
                    if (SMTCell::getNumTrack() == 2 && tmp_col != 0) {
                      // Just check all rows
                      FLAG_GATE_CUT = 1;
                    } else if (SMTCell::getNumTrack() == 3 && tmp_col != 0) {
                      // Just check all rows
                      FLAG_GATE_CUT = 1;
                    } else if (SMTCell::getNumTrack() == 4 && tmp_col != 0) {
                      // Just check all rows
                      FLAG_GATE_CUT = 1;
                    } else if (SMTCell::getNumTrack() == 5 && tmp_col != 0) {
                      fmt::print(stderr, "[ERROR] Gate CUT for 5 track has not "
                                         "been implemented.");
                      exit(1);
                    } else if (SMTCell::getNumTrack() == 6 && tmp_col != 0) {
                      fmt::print(stderr, "[ERROR] Gate CUT for 6 track has not "
                                         "been implemented.");
                      exit(1);
                    }
                    // write to constraint
                    const std::string metal_variable =
                        fmt::format("M_{}_{}", tmp_vname_first->getVName(),
                                    tmp_vname_second->getVName());
                    if (h_tmp.find(metal_variable) == h_tmp.end()) {
                      if (!SMTCell::ifAssigned(metal_variable)) {
                        // fmt::print("1 {}\n", metal_variable);
                        SMTCell::setVar(metal_variable, 2);
                        int col_ = tmp_col > 0
                                       ? (tmp_col - SMTCell::getMetalPitch(1))
                                       : tmp_col;
                        // check if we are in the middle rows
                        if (FLAG_GATE_CUT == 1) {
                          SMTCell::writeConstraint(fmt::format(
                              "(assert (ite (and (bvsge COST_SIZE (_ bv{} {})) "
                              "(= gc_s{}m1c{} false)) (= {} "
                              "true) (= {} false)))\n",
                              SMTCell::get_h_metal_col_idx(metal, col_),
                              SMTCell::getBitLength_numTrackV(), site_idx,
                              tmp_col, metal_variable, metal_variable));
                        } else {
                          SMTCell::writeConstraint(fmt::format(
                              "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= "
                              "{} "
                              "true) (= {} false)))\n",
                              SMTCell::get_h_metal_col_idx(metal, col_),
                              SMTCell::getBitLength_numTrackV(), metal_variable,
                              metal_variable));
                        }
                        h_tmp[metal_variable] = 1;
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("c", 1);
                      }
                    }
                  }
                } else {
                  // NMOS
                  for (int i = 0; i <= height - 2; i++) {
                    int j = SMTCell::getNumTrackH() - 2 - height + i;
                    int k = j + 1;
                    tmp_vname_first->setRow(
                        SMTCell::
                            get_routing_row_by_site_idx_and_metal_and_row_idx(
                                site_idx, metal, j));
                    tmp_vname_second->setRow(
                        SMTCell::
                            get_routing_row_by_site_idx_and_metal_and_row_idx(
                                site_idx, metal, k));
                    // GC FLAG: check if gc is enabled or not before setting any
                    // gate variables GC FLAG: never need to cut gate 0
                    int FLAG_GATE_CUT = 0;
                    if (SMTCell::getNumTrack() == 2 && tmp_col != 0) {
                      FLAG_GATE_CUT = 1;
                    } else if (SMTCell::getNumTrack() == 3 && tmp_col != 0) {
                      FLAG_GATE_CUT = 1;
                    } else if (SMTCell::getNumTrack() == 4 && tmp_col != 0) {
                      FLAG_GATE_CUT = 1;
                    } else if (SMTCell::getNumTrack() == 5 && tmp_col != 0) {
                      fmt::print(stderr, "[ERROR] Gate CUT for 5 track has not "
                                         "been implemented.");
                      exit(1);
                    } else if (SMTCell::getNumTrack() == 6 && tmp_col != 0) {
                      fmt::print(stderr, "[ERROR] Gate CUT for 6 track has not "
                                         "been implemented.");
                      exit(1);
                    }
                    // write to constraint
                    std::string metal_variable =
                        fmt::format("M_{}_{}", tmp_vname_first->getVName(),
                                    tmp_vname_second->getVName());
                    if (h_tmp.find(metal_variable) == h_tmp.end()) {
                      if (!SMTCell::ifAssigned(metal_variable)) {
                        // fmt::print("2 {}\n", metal_variable);
                        SMTCell::setVar(metal_variable, 2);
                        int col_ = tmp_col > 0
                                       ? (tmp_col - SMTCell::getMetalPitch(1))
                                       : tmp_col;
                        if (FLAG_GATE_CUT == 1) {
                          SMTCell::writeConstraint(fmt::format(
                              "(assert (ite (and (bvsge COST_SIZE (_ bv{} {})) "
                              "(= gc_s{}m1c{} false)) (= {} "
                              "true) (= {} false)))\n",
                              SMTCell::get_h_metal_col_idx(metal, col_),
                              SMTCell::getBitLength_numTrackV(), site_idx,
                              tmp_col, metal_variable, metal_variable));
                        } else {
                          SMTCell::writeConstraint(fmt::format(
                              "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= "
                              "{} "
                              "true) (= {} false)))\n",
                              SMTCell::get_h_metal_col_idx(metal, col_),
                              SMTCell::getBitLength_numTrackV(), metal_variable,
                              metal_variable));
                        }
                        h_tmp[metal_variable] = 1;
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("c", 1);
                      }
                    }
                  }
                }

                delete tmp_vname_first;
                delete tmp_vname_second;
              }
            }
          } else if (tmp_ve->getPinName() == sinkPin) {
            if (tmp_ve->getPinName() != Pin::keySON) {
              // Pin *pin_t = SMTCell::getPin(sinkPin);
              std::shared_ptr<Pin> pin_t = SMTCell::getPin(sinkPin);
              // external net should NOT be considered
              if (pin_t->getInstID() == "ext") {
                continue;
              }
              // instance index
              int instIdx = SMTCell::getPinInstIdx(pin_t);
              std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
                  SMTCell::getInst(instIdx)->getInstWidth(),
                  SMTCell::getTrackEachPRow());

              // fixed value, should be variable
              int metal = 1; // AGR FLAG: placement only considers M1
              int height = 3;

              if (SMTCell::getNumTrack() == 2) {
                height = 2;
              } else if (SMTCell::getNumTrack() == 3) {
                height = 3;
              }

              // Source pin is Gate
              if (SMTCell::getPin(sinkPin)->getPinType() == Pin::GATE) {
                // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
                int tmp_col = tmp_ve->getVCoord()->col_;
                if (SMTCell::ifGCol_AGR(metal, tmp_col)) {
                  // use copy constructor
                  Triplet *tmp_vname_first = new Triplet(*tmp_ve->getVCoord());
                  Triplet *tmp_vname_second = new Triplet(*tmp_ve->getVCoord());
                  // PMOS
                  if (instIdx <= SMTCell::getLastIdxPMOS()) {
                    for (int i = 0; i < height - 1; i++) {
                      int j = i;
                      int k = j + 1;
                      // fmt::print("i: {}, j: {}, k: {}\n", i, j, k);
                      tmp_vname_first->setRow(
                          SMTCell::
                              get_routing_row_by_site_idx_and_metal_and_row_idx(
                                  site_idx, metal, j));
                      tmp_vname_second->setRow(
                          SMTCell::
                              get_routing_row_by_site_idx_and_metal_and_row_idx(
                                  site_idx, metal, k));
                      // write to constraint
                      const std::string metal_variable =
                          fmt::format("M_{}_{}", tmp_vname_first->getVName(),
                                      tmp_vname_second->getVName());
                      if (h_tmp.find(metal_variable) == h_tmp.end()) {
                        if (!SMTCell::ifAssigned(metal_variable)) {
                          SMTCell::setVar(metal_variable, 2);
                          SMTCell::writeConstraint(fmt::format(
                              "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= "
                              "{} "
                              "true) (= {} false)))\n",
                              SMTCell::get_h_metal_col_idx(
                                  metal,
                                  (tmp_col > 0
                                       ? (tmp_col - SMTCell::getMetalPitch(1))
                                       : tmp_col)),
                              SMTCell::getBitLength_numTrackV(), metal_variable,
                              metal_variable));
                          h_tmp[metal_variable] = 1;
                          SMTCell::cnt("l", 1);
                          SMTCell::cnt("l", 1);
                          SMTCell::cnt("l", 1);
                          SMTCell::cnt("c", 1);
                        }
                      }
                    }
                  } else {
                    // NMOS
                    for (int i = 0; i < height - 1; i++) {
                      int j = SMTCell::getNumTrackH() - 2 - height + i;
                      int k = j + 1;
                      tmp_vname_first->setRow(
                          SMTCell::
                              get_routing_row_by_site_idx_and_metal_and_row_idx(
                                  site_idx, metal, j));
                      tmp_vname_second->setRow(
                          SMTCell::
                              get_routing_row_by_site_idx_and_metal_and_row_idx(
                                  site_idx, metal, k));
                      // write to constraint
                      const std::string metal_variable =
                          fmt::format("M_{}_{}", tmp_vname_first->getVName(),
                                      tmp_vname_second->getVName());
                      if (h_tmp.find(metal_variable) == h_tmp.end()) {
                        if (!SMTCell::ifAssigned(metal_variable)) {
                          SMTCell::setVar(metal_variable, 2);
                          SMTCell::writeConstraint(fmt::format(
                              "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= "
                              "{} "
                              "true) (= {} false)))\n",
                              SMTCell::get_h_metal_col_idx(
                                  metal,
                                  (tmp_col > 0
                                       ? (tmp_col - SMTCell::getMetalPitch(1))
                                       : tmp_col)),
                              SMTCell::getBitLength_numTrackV(), metal_variable,
                              metal_variable));
                          h_tmp[metal_variable] = 1;
                          SMTCell::cnt("l", 1);
                          SMTCell::cnt("l", 1);
                          SMTCell::cnt("l", 1);
                          SMTCell::cnt("c", 1);
                        }
                      }
                    }
                  }
                  delete tmp_vname_first;
                  delete tmp_vname_second;
                }
              }
            }
          }
        }
      }
    }
  }
}

void Placement::unset_rightmost_metal() {
  // fmt::print(" MOS min width: {}\n", SMTCell::getMOSMinWidth());
  SMTCell::writeConstraint(";Unset All Metal/Net/Wire over the rightmost "
                           "cell/metal(>COST_SIZE+1)\n");
  // # Unset All Metal/Net/Wire over the rightmost cell/metal(>COST_SIZE+1)
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    // int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->col_;
    int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
    // int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->row_;
    // int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->row_;
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    if (fromMetal == toMetal && fromMetal == 1) {
      continue;
    }
    // this could equal to 2 because min possible width is 2 * 1 (# fingers)
    // if (SMTCell::getMOSMinWidth() > 2 &&
    //     toCol > SMTCell::getMOSMinWidth() - 2) {
    if (SMTCell::getMOSMinWidth() >= 2 &&
        toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalPitch(1) &&
        (toCol - 1 * SMTCell::getMetalPitch(1)) >= 0) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (!SMTCell::ifAssigned(variable_name)) {
        SMTCell::setVar(variable_name, 2);
        // SMTCell::writeConstraint(fmt::format(
        //     "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
        //     "false) (= true true)))\n",
        //     (toCol - 2), SMTCell::getBitLength_numTrackV(), variable_name));
        SMTCell::writeConstraint(
            fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                        "false) (= true true)))\n",
                        SMTCell::get_h_metal_col_idx(
                            1, toCol - 1 * SMTCell::getMetalPitch(1)),
                        SMTCell::getBitLength_numTrackV(), variable_name));
        SMTCell::cnt("l", 1);
        SMTCell::cnt("l", 1);
        SMTCell::cnt("c", 1);
      }
    }

    // Disable boundary column usage to improve abutment
    // if (fromMetal == toMetal && fromMetal == 3) {
    //   if (toCol == 0 && fromCol == 0) {
    //     SMTCell::writeConstraint(fmt::format(
    //         "(assert (= {} false))\n",
    //         fmt::format(
    //             "M_{}_{}",
    //             SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
    //             SMTCell::getUdEdge(udEdgeIndex)
    //                 ->getUdEdgeToVar()
    //                 ->getVName())));
    //   }
    // }
  }

  // SMTCell::dump_h_assign();
  SMTCell::writeConstraint(";0.0.1. Net/Edge\n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
         udEdgeIndex++) {
      // int fromCol =
      // SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->col_;
      int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
      // int fromRow =
      // SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->row_; int toRow =
      // SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->row_;
      int fromMetal =
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
      int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
      if (fromMetal == toMetal && fromMetal == 1) {
        continue;
      }
      if (SMTCell::getMOSMinWidth() >= 2 &&
          toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalPitch(1) &&
          (toCol - 1 * SMTCell::getMetalPitch(1)) >= 0) {
        std::string variable_name = fmt::format(
            "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
        if (!SMTCell::ifAssigned(variable_name)) {
          SMTCell::setVar(variable_name, 2);
          SMTCell::writeConstraint(
              fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                          "false) (= true true)))\n",
                          SMTCell::get_h_metal_col_idx(
                              1, toCol - 1 * SMTCell::getMetalPitch(1)),
                          SMTCell::getBitLength_numTrackV(), variable_name));
          SMTCell::cnt("l", 1);
          SMTCell::cnt("l", 1);
          SMTCell::cnt("c", 1);
        }
      }
    }
  }

  // SMTCell::writeConstraint(";line 3438 \n");
  SMTCell::writeConstraint(";0.0.2. Net/Commodity/Edge\n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;

        // exclude M1 only edges
        if (fromMetal == toMetal && fromMetal == 1) {
          continue;
        }
        // fmt::print("HERE! minWidth {} toCol {} \n",
        // SMTCell::getMOSMinWidth(),
        //            toCol);
        if (SMTCell::getMOSMinWidth() >= 2 &&
            toCol >
                (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalPitch(1) &&
            (toCol - 1 * SMTCell::getMetalPitch(1)) >= 0) {
          // missing N1 C1 here
          std::string variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex,
              SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
              SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
          // if (SMTCell::getNet(netIndex)->getNetID() == "1") {
          //   fmt::print("HERE! {} Ifassigned? {}\n", variable_name,
          //              SMTCell::ifAssigned(variable_name));
          // }
          // bug found previously assigned
          if (!SMTCell::ifAssigned(variable_name)) {
            // fmt::print("HERE!\n");
            SMTCell::setVar(variable_name, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                            "false) (= true true)))\n",
                            SMTCell::get_h_metal_col_idx(
                                1, toCol - (1 * SMTCell::getMetalPitch(1))),
                            SMTCell::getBitLength_numTrackV(), variable_name));
            SMTCell::cnt("l", 1);
            SMTCell::cnt("l", 1);
            SMTCell::cnt("c", 1);
          }
        }

        // Disable boundary column usage to improve abutment
        // if (fromMetal == toMetal && fromMetal == 3) {
        //   if (toCol == 0 && fromCol == 0) {
        //     SMTCell::writeConstraint(
        //         fmt::format("(assert (= {} false))\n",
        //                     fmt::format("N{}_C{}_E_{}_{}",
        //                                 SMTCell::getNet(netIndex)->getNetID(),
        //                                 commodityIndex,
        //                                 SMTCell::getUdEdge(udEdgeIndex)
        //                                     ->getUdEdgeFromVar()
        //                                     ->getVName(),
        //                                 SMTCell::getUdEdge(udEdgeIndex)
        //                                     ->getUdEdgeToVar()
        //                                     ->getVName())));
        //   }
        // }
      }
    }
  }

  // SMTCell::writeConstraint("; has issue flag ^\n");
  SMTCell::writeConstraint(";0.0.3. Net/VirtualEdge\n");
  for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
       vEdgeIndex++) {
    int toCol = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
    if (SMTCell::getMOSMinWidth() > 2 &&
        toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalPitch(1) &&
        (toCol - (2 * SMTCell::getMetalPitch(1))) >= 0) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->getVName(),
          SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
      if (!SMTCell::ifAssigned(variable_name)) {
        SMTCell::setVar(variable_name, 2);
        SMTCell::writeConstraint(
            fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                        "false) (= true true)))\n",
                        SMTCell::get_h_metal_col_idx(
                            1, toCol - (2 * SMTCell::getMetalPitch(1))),
                        SMTCell::getBitLength_numTrackV(), variable_name));
        SMTCell::cnt("l", 1);
        SMTCell::cnt("l", 1);
        SMTCell::cnt("c", 1);
      }
    }
  }

  SMTCell::writeConstraint(";0.0.4. Net/VirtualEdge\n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
         vEdgeIndex++) {
      int toCol = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
      if (SMTCell::getMOSMinWidth() >= 2 &&
          toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalPitch(1) &&
          (toCol - (2 * SMTCell::getMetalPitch(1))) >
              0) { // AGR FLAG: prevent negative
        // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
        std::shared_ptr<VirtualEdge> tmp_ve =
            SMTCell::getVirtualEdge(vEdgeIndex);
        std::string sourcePin = SMTCell::getNet(netIndex)->getSource_ofNet();
        // Source pin
        if (tmp_ve->getPinName() == sourcePin) {
          std::string variable_name = fmt::format(
              "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              tmp_ve->getVCoord()->getVName(), tmp_ve->getPinName());
          if (!SMTCell::ifAssigned(variable_name)) {
            SMTCell::setVar(variable_name, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                            "false) (= true true)))\n",
                            SMTCell::get_h_metal_col_idx(
                                1, toCol - (2 * SMTCell::getMetalPitch(1))),
                            SMTCell::getBitLength_numTrackV(), variable_name));
            SMTCell::cnt("l", 1);
            SMTCell::cnt("l", 1);
            SMTCell::cnt("c", 1);
          }
        } else {
          // Sink pin
          for (int commodityIndex = 0;
               commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
               commodityIndex++) {
            std::string sinkPin =
                SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
            if (tmp_ve->getPinName() == sinkPin) {
              std::string variable_name = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  tmp_ve->getVCoord()->getVName(), tmp_ve->getPinName());
              if (!SMTCell::ifAssigned(variable_name)) {
                SMTCell::setVar(variable_name, 2);
                SMTCell::writeConstraint(fmt::format(
                    "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                    "false) (= true true)))\n",
                    SMTCell::get_h_metal_col_idx(
                        1, toCol - (2 * SMTCell::getMetalPitch(1))),
                    SMTCell::getBitLength_numTrackV(), variable_name));
                SMTCell::cnt("l", 1);
                SMTCell::cnt("l", 1);
                SMTCell::cnt("c", 1);
              }
            }
          }
        }
      }
    }
  }

  // SMTCell::writeConstraint(";line 3505 \n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
         vEdgeIndex++) {
      // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
      std::shared_ptr<VirtualEdge> tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
      int toCol = tmp_ve->getVCoord()->col_;
      // ignored metals since not used
      if (SMTCell::getMOSMinWidth() >= 2 &&
          toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalPitch(1) &&
          (toCol - 2 * SMTCell::getMetalPitch(1)) >
              0) { // AGR FLAG: prevent negative
        for (int commodityIndex = 0;
             commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex++) {
          std::string sourcePin = SMTCell::getNet(netIndex)->getSource_ofNet();
          std::string sinkPin =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
          std::string variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, tmp_ve->getVCoord()->getVName(),
              tmp_ve->getPinName());
          // if (tmp_ve->getPinName() == sourcePin || sinkPin == sourcePin) {
          //   if (!SMTCell::ifAssigned(variable_name)) {
          //     SMTCell::setVar(variable_name, 2);
          //     SMTCell::writeConstraint(fmt::format(
          //         "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
          //         "false) (= true true)))\n",
          //         (toCol - 2), SMTCell::getBitLength_numTrackV(),
          //         variable_name));
          //     SMTCell::cnt("l", 1);
          //     SMTCell::cnt("l", 1);
          //     SMTCell::cnt("c", 1);
          //   }
          // }
          if (tmp_ve->getPinName() == sourcePin ||
              tmp_ve->getPinName() == sinkPin) {
            if (!SMTCell::ifAssigned(variable_name)) {
              SMTCell::setVar(variable_name, 2);
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                  "false) (= true true)))\n",
                  SMTCell::get_h_metal_col_idx(
                      1, toCol - 2 * SMTCell::getMetalPitch(1)),
                  SMTCell::getBitLength_numTrackV(), variable_name));
              SMTCell::cnt("l", 1);
              SMTCell::cnt("l", 1);
              SMTCell::cnt("c", 1);
            }
          }
        }
      }
    }
  }
}

void Placement::localize_adjacent_pin(int local_Parameter) {
  if (local_Parameter == 1) {
    SMTCell::writeConstraint(";Localization.\n\n");
    SMTCell::writeConstraint(
        ";Localization for Adjacent Pins in the same multifinger TRs.\n\n");
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        // inst pin idx
        std::string pin_idx_source =
            SMTCell::getNet(netIndex)->getSource_ofNet();
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        // external net should NOT be considered
        if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
          continue;
        }
        // pin ptr
        std::shared_ptr<Pin> pin_s = SMTCell::getPin(pin_idx_source);
        std::shared_ptr<Pin> pin_t = SMTCell::getPin(pin_idx_sink);
        // external net should NOT be considered
        if (pin_s->getInstID() == "ext" || pin_t->getInstID() == "ext") {
          continue;
        }
        // inst idx
        int inst_pin_s = SMTCell::getPinInstIdx(pin_s);
        int inst_pin_t = SMTCell::getPinInstIdx(pin_t);
        // type
        std::string type_s = pin_s->getPinType();
        std::string type_t = pin_t->getPinType();

        if (pin_idx_sink != Pin::keySON) {
          // skip if s/t same inst
          if (inst_pin_s == inst_pin_t) {
            for (int metal = 3; metal <= SMTCell::getNumMetalLayer(); metal++) {
              for (int row_idx = 0;
                   row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3;
                   row_idx++) {
                for (int col_idx = 0;
                     col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
                     col_idx++) {
                  // retrieve row/col
                  int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
                  int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
                  Triplet vCoord = Triplet(metal, row, col);
                  // incoming
                  if (SMTCell::ifEdgeIn(vCoord.getVName())) {
                    for (int i : SMTCell::getEdgeIn(vCoord.getVName())) {
                      SMTCell::assignTrueVar(
                          SMTCell::getNet(netIndex)->getNetID(), commodityIndex,
                          SMTCell::getUdEdge(i)->getUdEdgeFromVar()->getVName(),
                          vCoord.getVName(), 0, false);
                    }
                  }

                  if (SMTCell::ifEdgeOut(vCoord.getVName())) {
                    // outgoing
                    for (int i : SMTCell::getEdgeOut(vCoord.getVName())) {
                      SMTCell::assignTrueVar(
                          SMTCell::getNet(netIndex)->getNetID(), commodityIndex,
                          vCoord.getVName(), SMTCell::getUdEdgeToVarName(i), 0,
                          false);
                    }
                  }
                }
              }
            }

            if (type_s != Pin::GATE || type_t != Pin::GATE) {
              for (int metal = 1; metal <= 2; metal++) {
                for (int col_idx = 0;
                     col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
                     col_idx++) {
                  int lowRow = 0;
                  int upRow = 0;
                  if (inst_pin_s <= SMTCell::getLastIdxPMOS()) {
                    lowRow = SMTCell::getNumTrackH() / 2 - 1;
                    upRow = SMTCell::getNumTrackH() - 3;
                  } else {
                    lowRow = 0;
                    upRow = SMTCell::getNumTrackH() / 2 - 2;
                  }
                  // retrieve col
                  int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
                  // AGR FLAG: no change to rows for now
                  for (int row = lowRow; row <= upRow; row++) {
                    Triplet vCoord = Triplet(metal, row, col);
                    // incoming
                    if (SMTCell::ifEdgeIn(vCoord.getVName())) {
                      for (int i : SMTCell::getEdgeIn(vCoord.getVName())) {
                        SMTCell::assignTrueVar(
                            SMTCell::getNet(netIndex)->getNetID(),
                            commodityIndex,
                            SMTCell::getUdEdge(i)
                                ->getUdEdgeFromVar()
                                ->getVName(),
                            vCoord.getVName(), 0, false);
                      }
                    }
                    // outgoing
                    if (SMTCell::ifEdgeOut(vCoord.getVName())) {
                      for (int i : SMTCell::getEdgeOut(vCoord.getVName())) {
                        SMTCell::assignTrueVar(
                            SMTCell::getNet(netIndex)->getNetID(),
                            commodityIndex, vCoord.getVName(),
                            SMTCell::getUdEdgeToVarName(i), 0, false);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

void Placement::remove_x_symmetric_placement(FILE *fp, bool BS_Parameter) {
  if (BS_Parameter == 1) {
    fmt::print(fp, ";Removing Symmetric Placement Cases\n");
    int numPMOS = SMTCell::getLastIdxPMOS() + 1;
    int numNMOS = SMTCell::getNumInstance() - numPMOS;
    std::vector<int> arr_pmos;
    std::vector<int> arr_nmos;

    for (int i = 0; i < SMTCell::getLastIdxPMOS() + 1; i++) {
      arr_pmos.push_back(i);
    }

    for (int i = SMTCell::getLastIdxPMOS() + 1; i < SMTCell::getNumInstance();
         i++) {
      arr_nmos.push_back(i);
    }

    std::vector<std::vector<int>> comb_l_pmos = {};
    std::vector<std::vector<int>> comb_l_nmos = {};
    std::vector<std::vector<int>> comb_c_pmos = {};
    std::vector<std::vector<int>> comb_c_nmos = {};
    std::vector<std::vector<int>> comb_r_pmos = {};
    std::vector<std::vector<int>> comb_r_nmos = {};

    // PMOS
    if (numPMOS % 2 == 0) {
      std::vector<std::vector<int>> tmp_comb_l_pmos =
          SMTCell::combine(arr_pmos, numPMOS / 2);
      for (std::size_t i = 0; i < tmp_comb_l_pmos.size(); i++) {
        // fmt::print("#1 [RM PMOS sysmetry] {}\n", i);
        std::vector<int> tmp_comb;
        int isComb = 0;
        for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
          // avoid SEGFAULT
          if (tmp_comb_l_pmos.size() > i) {
            for (std::size_t k = 0; k < tmp_comb_l_pmos[i].size(); k++) {
              if (tmp_comb_l_pmos[i][k] == j) {
                isComb = 1;
                break;
              }
            }
          }
          if (isComb == 0) {
            tmp_comb.push_back(j);
          }
          isComb = 0;
        }
        // avoid SEGFAULT
        if (tmp_comb_l_pmos.size() > i) {
          comb_l_pmos.push_back(tmp_comb_l_pmos[i]);
        }
        comb_r_pmos.push_back(tmp_comb);
        if (tmp_comb_l_pmos.size() - 1 == 1) {
          break;
        }
      }
    } else {
      for (int m = 0; m < numPMOS; m++) {
        // fmt::print("#2 [RM PMOS sysmetry] {}\n", m);
        arr_pmos.clear();
        for (int i = 0; i <= SMTCell::getLastIdxPMOS(); i++) {
          if (i != m) {
            arr_pmos.push_back(i);
          }
        }
        std::vector<std::vector<int>> tmp_comb_l_pmos =
            SMTCell::combine(arr_pmos, (numPMOS - 1) / 2);

        for (std::size_t i = 0; i < tmp_comb_l_pmos.size(); i++) {
          std::vector<int> tmp_comb;
          int isComb = 0;
          for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
            // avoid SEGFAULT
            if (tmp_comb_l_pmos.size() > i) {
              for (std::size_t k = 0; k < tmp_comb_l_pmos[i].size(); k++) {
                if (tmp_comb_l_pmos[i][k] == j || j == m) {
                  isComb = 1;
                  break;
                }
              }
            }
            if (isComb == 0) {
              tmp_comb.push_back(j);
            }
            isComb = 0;
          }

          // avoid SEGFAULT
          if (tmp_comb_l_pmos.size() > i) {
            comb_l_pmos.push_back(tmp_comb_l_pmos[i]);
          }
          comb_r_pmos.push_back(tmp_comb);
          comb_c_pmos.push_back({m});

          if (tmp_comb_l_pmos.size() - 1 == 1) {
            break;
          }
        }
      }
    }

    // NMOS
    if (numNMOS % 2 == 0) {
      std::vector<std::vector<int>> tmp_comb_l_nmos =
          SMTCell::combine(arr_nmos, numNMOS / 2);
      for (std::size_t i = 0; i < tmp_comb_l_nmos.size(); i++) {
        // fmt::print("#3 [RM NMOS sysmetry] {}\n", i);
        std::vector<int> tmp_comb;
        int isComb = 0;
        for (int j = SMTCell::getLastIdxPMOS() + 1;
             j < SMTCell::getNumInstance(); ++j) {
          // fmt::print("#3-1 [RM NMOS sysmetry] {}\n", j);
          // check vec size to prevent SEGFAULT
          if (tmp_comb_l_nmos.size() > i) {
            for (std::size_t k = 0; k < tmp_comb_l_nmos[i].size(); ++k) {
              // fmt::print("#3-2 [RM NMOS sysmetry] {}\n", k);
              if (tmp_comb_l_nmos[i][k] == j) {
                isComb = 1;
                break;
              }
            }
          }
          if (isComb == 0) {
            tmp_comb.push_back(j);
          }
          isComb = 0;
        }
        if (tmp_comb_l_nmos.size() > i) {
          comb_l_nmos.push_back(tmp_comb_l_nmos[i]);
        }
        comb_r_nmos.push_back(tmp_comb);
        if (tmp_comb_l_nmos.size() - 1 == 1) {
          break;
        }
      }
    } else {
      for (int m = SMTCell::getLastIdxPMOS() + 1; m < SMTCell::getNumInstance();
           m++) {
        // fmt::print("#4 [RM NMOS sysmetry] {}\n", m);
        arr_nmos.clear();

        for (int i = 0; i < numNMOS; i++) {
          if (i + SMTCell::getLastIdxPMOS() + 1 != m) {
            arr_nmos.push_back(i + SMTCell::getLastIdxPMOS() + 1);
          }
        }

        std::vector<std::vector<int>> tmp_comb_l_nmos =
            SMTCell::combine(arr_nmos, (numNMOS - 1) / 2);

        for (std::size_t i = 0; i < tmp_comb_l_nmos.size(); i++) {
          std::vector<int> tmp_comb;
          int isComb = 0;
          for (int j = SMTCell::getLastIdxPMOS() + 1;
               j < SMTCell::getNumInstance(); j++) {
            // avoid SEGFAULT
            if (tmp_comb_l_nmos.size() > i) {
              for (std::size_t k = 0; k < tmp_comb_l_nmos[i].size(); k++) {
                if (tmp_comb_l_nmos[i][k] == j || j == m) {
                  isComb = 1;
                  break;
                }
              }
            }
            if (isComb == 0) {
              tmp_comb.push_back(j);
            }
            isComb = 0;
          }
          // avoid SEGFAULT
          if (tmp_comb_l_nmos.size() > i) {
            comb_l_nmos.push_back(tmp_comb_l_nmos[i]);
          }
          comb_r_nmos.push_back(tmp_comb);
          comb_c_nmos.push_back({m});

          if (tmp_comb_l_nmos.size() - 1 == 1) {
            break;
          }
        }
      }
    }

    for (std::size_t i = 0; i < comb_l_pmos.size(); ++i) {
      fmt::print(fp, "(assert (or");

      if (comb_l_pmos.size() <= i) {
        continue;
      } // prevent segfault

      for (std::size_t l = 0; l < comb_l_pmos[i].size(); ++l) {
        if (comb_r_pmos.size() <= i) {
          continue;
        } // prevent segfault
        for (std::size_t m = 0; m < comb_r_pmos[i].size(); ++m) {
          fmt::print(fp, " (bvsle x{} x{})", comb_l_pmos[i][l],
                     comb_r_pmos[i][m]);
          SMTCell::cnt("l", 0);

          if (comb_c_pmos.size() <= i) {
            continue;
          } // prevent segfault
          // fmt::print("{}\n", i);
          for (std::size_t n = 0; n < comb_c_pmos[i].size(); ++n) {
            fmt::print(fp, " (bvsle x{} x{})", comb_l_pmos[i][l],
                       comb_c_pmos[i][n]);
            fmt::print(fp, " (bvsge x{} x{})", comb_r_pmos[i][m],
                       comb_c_pmos[i][n]);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
          }
        }
      }
      fmt::print(fp, " (and");

      for (std::size_t j = 0; j < comb_l_nmos.size(); ++j) {
        fmt::print(fp, " (or");
        if (comb_l_nmos.size() <= i) {
          continue;
        } // prevent segfault

        for (std::size_t l = 0; l < comb_l_nmos[j].size(); ++l) {
          if (comb_r_nmos.size() <= i) {
            continue;
          } // prevent segfault
          for (std::size_t m = 0; m < comb_r_nmos[j].size(); ++m) {
            fmt::print(fp, " (bvsle x{} x{})", comb_l_nmos[j][l],
                       comb_r_nmos[j][m]);
            SMTCell::cnt("l", 0);

            if (comb_c_nmos.size() <= i) {
              continue;
            } // prevent segfault
            // fmt::print("{}\n", j);
            for (std::size_t n = 0; n < comb_c_nmos[j].size(); ++n) {
              fmt::print(fp, " (bvsle x{} x{})", comb_l_nmos[j][l],
                         comb_c_nmos[j][n]);
              fmt::print(fp, " (bvsge x{} x{})", comb_r_nmos[j][m],
                         comb_c_nmos[j][n]);
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
            }
          }
        }
        fmt::print(fp, ")");
      }
      fmt::print(fp, ")))\n");
      SMTCell::cnt("c", 0);
    }

    fmt::print(fp, ";Set flip status to false for FETs which have even "
                   "numbered fingers\n");
    for (int i = 0; i <= SMTCell::getLastIdxPMOS(); i++) {
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      if (tmp_finger[0] % 2 == 0) {
        fmt::print(fp, "(assert (= ff{} false))\n", i);
        SMTCell::cnt("l", 0);
        SMTCell::cnt("c", 0);
      }
    }
    for (int i = SMTCell::getNumPMOS(); i < SMTCell::getNumInstance(); i++) {
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      if (tmp_finger[0] % 2 == 0) {
        fmt::print(fp, "(assert (= ff{} false))\n", i);
        SMTCell::cnt("l", 0);
        SMTCell::cnt("c", 0);
      }
    }
    fmt::print(fp, ";End of X Symmetric Removal\n");
  }
}

void Placement::remove_y_symmetric_placement(FILE *fp, bool BS_Parameter) {
  if (BS_Parameter == 1) {
    fmt::print(fp, ";Removing Symmetric Placement Cases\n");
    int numPMOS = SMTCell::getLastIdxPMOS() + 1;
    int numNMOS = SMTCell::getNumInstance() - numPMOS;
    std::vector<int> arr_pmos;
    std::vector<int> arr_nmos;

    for (int i = 0; i < SMTCell::getLastIdxPMOS() + 1; i++) {
      arr_pmos.push_back(i);
    }

    for (int i = SMTCell::getLastIdxPMOS() + 1; i < SMTCell::getNumInstance();
         i++) {
      arr_nmos.push_back(i);
    }

    std::vector<std::vector<int>> comb_l_pmos = {};
    std::vector<std::vector<int>> comb_l_nmos = {};
    std::vector<std::vector<int>> comb_c_pmos = {};
    std::vector<std::vector<int>> comb_c_nmos = {};
    std::vector<std::vector<int>> comb_r_pmos = {};
    std::vector<std::vector<int>> comb_r_nmos = {};

    // PMOS
    if (numPMOS % 2 == 0) {
      std::vector<std::vector<int>> tmp_comb_l_pmos =
          SMTCell::combine(arr_pmos, numPMOS / 2);
      for (std::size_t i = 0; i < tmp_comb_l_pmos.size(); i++) {
        // fmt::print("#1 [RM PMOS sysmetry] {}\n", i);
        std::vector<int> tmp_comb;
        int isComb = 0;
        for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
          // avoid SEGFAULT
          if (tmp_comb_l_pmos.size() > i) {
            for (std::size_t k = 0; k < tmp_comb_l_pmos[i].size(); k++) {
              if (tmp_comb_l_pmos[i][k] == j) {
                isComb = 1;
                break;
              }
            }
          }
          if (isComb == 0) {
            tmp_comb.push_back(j);
          }
          isComb = 0;
        }
        // avoid SEGFAULT
        if (tmp_comb_l_pmos.size() > i) {
          comb_l_pmos.push_back(tmp_comb_l_pmos[i]);
        }
        comb_r_pmos.push_back(tmp_comb);
        if (tmp_comb_l_pmos.size() - 1 == 1) {
          break;
        }
      }
    } else {
      for (int m = 0; m < numPMOS; m++) {
        // fmt::print("#2 [RM PMOS sysmetry] {}\n", m);
        arr_pmos.clear();
        for (int i = 0; i <= SMTCell::getLastIdxPMOS(); i++) {
          if (i != m) {
            arr_pmos.push_back(i);
          }
        }
        std::vector<std::vector<int>> tmp_comb_l_pmos =
            SMTCell::combine(arr_pmos, (numPMOS - 1) / 2);
        for (std::size_t i = 0; i < tmp_comb_l_pmos.size(); i++) {
          std::vector<int> tmp_comb;
          int isComb = 0;
          for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
            // avoid SEGFAULT
            if (tmp_comb_l_pmos.size() > i) {
              for (std::size_t k = 0; k < tmp_comb_l_pmos[i].size(); k++) {
                if (tmp_comb_l_pmos[i][k] == j || j == m) {
                  isComb = 1;
                  break;
                }
              }
            }
            if (isComb == 0) {
              tmp_comb.push_back(j);
            }
            isComb = 0;
          }

          // avoid SEGFAULT
          if (tmp_comb_l_pmos.size() > i) {
            comb_l_pmos.push_back(tmp_comb_l_pmos[i]);
          }
          comb_r_pmos.push_back(tmp_comb);
          comb_c_pmos.push_back({m});

          if (tmp_comb_l_pmos.size() - 1 == 1) {
            break;
          }
        }
      }
    }

    // NMOS
    if (numNMOS % 2 == 0) {
      std::vector<std::vector<int>> tmp_comb_l_nmos =
          SMTCell::combine(arr_nmos, numNMOS / 2);
      for (std::size_t i = 0; i < tmp_comb_l_nmos.size(); i++) {
        // fmt::print("#3 [RM NMOS sysmetry] {}\n", i);
        std::vector<int> tmp_comb;
        int isComb = 0;
        for (int j = SMTCell::getLastIdxPMOS() + 1;
             j < SMTCell::getNumInstance(); ++j) {
          // fmt::print("#3-1 [RM NMOS sysmetry] {}\n", j);
          // check vec size to prevent SEGFAULT
          if (tmp_comb_l_nmos.size() > i) {
            for (std::size_t k = 0; k < tmp_comb_l_nmos[i].size(); ++k) {
              // fmt::print("#3-2 [RM NMOS sysmetry] {}\n", k);
              if (tmp_comb_l_nmos[i][k] == j) {
                isComb = 1;
                break;
              }
            }
          }
          if (isComb == 0) {
            tmp_comb.push_back(j);
          }
          isComb = 0;
        }
        if (tmp_comb_l_nmos.size() > i) {
          comb_l_nmos.push_back(tmp_comb_l_nmos[i]);
        }
        comb_r_nmos.push_back(tmp_comb);
        if (tmp_comb_l_nmos.size() - 1 == 1) {
          break;
        }
      }
    } else {
      for (int m = SMTCell::getLastIdxPMOS() + 1; m < SMTCell::getNumInstance();
           m++) {
        // fmt::print("#4 [RM NMOS sysmetry] {}\n", m);
        arr_nmos.clear();

        for (int i = 0; i < numNMOS; i++) {
          if (i + SMTCell::getLastIdxPMOS() + 1 != m) {
            arr_nmos.push_back(i + SMTCell::getLastIdxPMOS() + 1);
          }
        }

        std::vector<std::vector<int>> tmp_comb_l_nmos =
            SMTCell::combine(arr_nmos, (numNMOS - 1) / 2);

        for (std::size_t i = 0; i < tmp_comb_l_nmos.size(); i++) {
          std::vector<int> tmp_comb;
          int isComb = 0;
          for (int j = SMTCell::getLastIdxPMOS() + 1;
               j < SMTCell::getNumInstance(); j++) {
            // avoid SEGFAULT
            if (tmp_comb_l_nmos.size() > i) {
              for (std::size_t k = 0; k < tmp_comb_l_nmos[i].size(); k++) {
                if (tmp_comb_l_nmos[i][k] == j || j == m) {
                  isComb = 1;
                  break;
                }
              }
            }
            if (isComb == 0) {
              tmp_comb.push_back(j);
            }
            isComb = 0;
          }
          // avoid SEGFAULT
          if (tmp_comb_l_nmos.size() > i) {
            comb_l_nmos.push_back(tmp_comb_l_nmos[i]);
          }
          comb_r_nmos.push_back(tmp_comb);
          comb_c_nmos.push_back({m});

          if (tmp_comb_l_nmos.size() - 1 == 1) {
            break;
          }
        }
      }
    }

    for (std::size_t i = 0; i < comb_l_pmos.size(); ++i) {
      fmt::print(fp, "(assert (or");

      if (comb_l_pmos.size() <= i) {
        continue;
      } // prevent segfault

      for (std::size_t l = 0; l < comb_l_pmos[i].size(); ++l) {
        if (comb_r_pmos.size() <= i) {
          continue;
        } // prevent segfault
        for (std::size_t m = 0; m < comb_r_pmos[i].size(); ++m) {
          fmt::print(fp, " (bvsle y{} y{})", comb_l_pmos[i][l],
                     comb_r_pmos[i][m]);
          SMTCell::cnt("l", 0);

          if (comb_c_pmos.size() <= i) {
            continue;
          } // prevent segfault
          // fmt::print("{}\n", i);
          for (std::size_t n = 0; n < comb_c_pmos[i].size(); ++n) {
            fmt::print(fp, " (bvsle y{} y{})", comb_l_pmos[i][l],
                       comb_c_pmos[i][n]);
            fmt::print(fp, " (bvsge y{} y{})", comb_r_pmos[i][m],
                       comb_c_pmos[i][n]);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
          }
        }
      }
      fmt::print(fp, " (and");

      for (std::size_t j = 0; j < comb_l_nmos.size(); ++j) {
        fmt::print(fp, " (or");
        if (comb_l_nmos.size() <= i) {
          continue;
        } // prevent segfault

        for (std::size_t l = 0; l < comb_l_nmos[j].size(); ++l) {
          if (comb_r_nmos.size() <= i) {
            continue;
          } // prevent segfault
          for (std::size_t m = 0; m < comb_r_nmos[j].size(); ++m) {
            fmt::print(fp, " (bvsle y{} y{})", comb_l_nmos[j][l],
                       comb_r_nmos[j][m]);
            SMTCell::cnt("l", 0);

            if (comb_c_nmos.size() <= i) {
              continue;
            } // prevent segfault
            // fmt::print("{}\n", j);
            for (std::size_t n = 0; n < comb_c_nmos[j].size(); ++n) {
              fmt::print(fp, " (bvsle y{} y{})", comb_l_nmos[j][l],
                         comb_c_nmos[j][n]);
              fmt::print(fp, " (bvsge y{} y{})", comb_r_nmos[j][m],
                         comb_c_nmos[j][n]);
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
            }
          }
        }
        fmt::print(fp, ")");
      }
      fmt::print(fp, ")))\n");
      SMTCell::cnt("c", 0);
    }

    for (std::size_t i = 0; i < comb_l_pmos.size(); ++i) {
      fmt::print(fp, "(assert (or");

      if (comb_l_pmos.size() <= i) {
        continue;
      } // prevent segfault

      for (std::size_t l = 0; l < comb_l_pmos[i].size(); ++l) {
        if (comb_r_pmos.size() <= i) {
          continue;
        } // prevent segfault
        for (std::size_t m = 0; m < comb_r_pmos[i].size(); ++m) {
          fmt::print(fp, " (bvsle y{} y{})", comb_l_pmos[i][l],
                     comb_r_pmos[i][m]);
          SMTCell::cnt("l", 0);

          if (comb_c_pmos.size() <= i) {
            continue;
          } // prevent segfault
          // fmt::print("{}\n", i);
          for (std::size_t n = 0; n < comb_c_pmos[i].size(); ++n) {
            fmt::print(fp, " (bvsle y{} y{})", comb_l_pmos[i][l],
                       comb_c_pmos[i][n]);
            fmt::print(fp, " (bvsge y{} y{})", comb_r_pmos[i][m],
                       comb_c_pmos[i][n]);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
          }
        }
      }
      fmt::print(fp, " (and");

      for (std::size_t j = 0; j < comb_l_nmos.size(); ++j) {
        fmt::print(fp, " (or");
        if (comb_l_nmos.size() <= i) {
          continue;
        } // prevent segfault

        for (std::size_t l = 0; l < comb_l_nmos[j].size(); ++l) {
          if (comb_r_nmos.size() <= i) {
            continue;
          } // prevent segfault
          for (std::size_t m = 0; m < comb_r_nmos[j].size(); ++m) {
            fmt::print(fp, " (bvsle y{} y{})", comb_l_nmos[j][l],
                       comb_r_nmos[j][m]);
            SMTCell::cnt("l", 0);

            if (comb_c_nmos.size() <= i) {
              continue;
            } // prevent segfault
            // fmt::print("{}\n", j);
            for (std::size_t n = 0; n < comb_c_nmos[j].size(); ++n) {
              fmt::print(fp, " (bvsle y{} y{})", comb_l_nmos[j][l],
                         comb_c_nmos[j][n]);
              fmt::print(fp, " (bvsge y{} y{})", comb_r_nmos[j][m],
                         comb_c_nmos[j][n]);
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
            }
          }
        }
        fmt::print(fp, ")");
      }
      fmt::print(fp, ")))\n");
      SMTCell::cnt("c", 0);
    }
    fmt::print(fp, ";Set flip status to false for FETs which have even "
                   "numbered fingers\n");
    for (int i = 0; i <= SMTCell::getLastIdxPMOS(); i++) {
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      if (tmp_finger[0] % 2 == 0) {
        fmt::print(fp, "(assert (= ff{} false))\n", i);
        SMTCell::cnt("l", 0);
        SMTCell::cnt("c", 0);
      }
    }
    for (int i = SMTCell::getNumPMOS(); i < SMTCell::getNumInstance(); i++) {
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      if (tmp_finger[0] % 2 == 0) {
        fmt::print(fp, "(assert (= ff{} false))\n", i);
        SMTCell::cnt("l", 0);
        SMTCell::cnt("c", 0);
      }
    }
    fmt::print(fp, ";End of Y Symmetric Removal\n");
  }
}

void Placement::init_placement_G_pin(std::string order_clip) {
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(
        fmt::format(";[SITE {}] Set Initial Value for Gate Pins of P/N FET in "
                    "the same column\n",
                    site_idx));
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string tmp_vname = "";
        // inst pin idx
        std::string pin_idx_source =
            SMTCell::getNet(netIndex)->getSource_ofNet();
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        // external net should NOT be considered
        if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
          continue;
        }
        // ignore startIdx and endIdx, not used
        std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        // external net should NOT be considered
        if (source_pin->getInstID() == "ext" ||
            sink_pin->getInstID() == "ext") {
          continue;
        }
        // ## Source MaxFlow Indicator
        int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
        // ## Sink MaxFlow Indicator
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        // finger
        std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(source_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());

        // ## Skip If Source/Sink TR is in the same region
        if ((source_inst_idx <= SMTCell::getLastIdxPMOS() &&
             sink_inst_idx <= SMTCell::getLastIdxPMOS()) ||
            (source_inst_idx > SMTCell::getLastIdxPMOS() &&
             sink_inst_idx > SMTCell::getLastIdxPMOS())) {
          continue;
        }

        // AGR FLAG: placement only consider metal 1
        int metal = 1;
        int row_source;
        int row_sink;
        row_source = SMTCell::get_mos_pin_row_by_site_idx(
            site_idx, SMTCell::ifInstPMOS(source_inst_idx));
        row_sink = SMTCell::get_mos_pin_row_by_site_idx(
            site_idx, SMTCell::ifInstPMOS(sink_inst_idx));
        // ## Skip if Source/Sink Pin is not "Gate" Pin
        if (source_pin->getPinType() != Pin::GATE ||
            sink_pin->getPinType() != Pin::GATE) {
          continue;
        }
        int tmp_pin_idx_source = std::stoi(std::regex_replace(
            pin_idx_source, std::regex("pin\\S+_(\\d+)"), "$1"));
        int tmp_pin_idx_sink = std::stoi(std::regex_replace(
            pin_idx_sink, std::regex("pin\\S+_(\\d+)"), "$1"));
        for (int col_idx = 0;
             col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1; col_idx++) {
          // retrieve col
          int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
          std::string tmp_str = "";
          std::vector<std::string> tmp_var_T;
          std::vector<std::string> tmp_var_F;
          int cnt_var_T = 0;
          int cnt_var_F = 0;

          Triplet vCoord;
          if (SMTCell::ifGCol_AGR(metal, col)) {
            // # Variables to Set True
            // Source
            vCoord = Triplet(1, row_source, col);
            std::string variable_name = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex, vCoord.getVName(), pin_idx_source);
            tmp_var_T.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            cnt_var_T++;

            vCoord = {}; // reset

            // Sink
            vCoord = Triplet(1, row_sink, col);
            variable_name = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex, vCoord.getVName(), pin_idx_sink);
            tmp_var_T.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            cnt_var_T++;

            for (auto row_idx_it = SMTCell::pmos_routing_rows_begin(site_idx);
                 row_idx_it != SMTCell::pmos_routing_rows_end(site_idx);
                 ++row_idx_it) {
              int row_idx = *row_idx_it;
              int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
              Triplet vCoordFront = Triplet(1, row, col);
              Triplet vCoordBack = Triplet(
                  1, SMTCell::get_h_metal_row_by_idx(metal, row_idx + 1), col);
              variable_name = fmt::format(
                  "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  commodityIndex, vCoordFront.getVName(),
                  vCoordBack.getVName());
              tmp_var_T.push_back(variable_name);
              SMTCell::setVar(variable_name, 2);
              cnt_var_T++;
            }

            // # Variables to Set False
            for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
                 udEdgeIndex++) {
              int fromCol =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->col_;
              int toCol =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
              int fromMetal =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
              int toMetal =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
              if (!(fromMetal == 1 && toMetal == 1 && fromCol == toCol &&
                    fromCol == col)) {
                variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex,
                    SMTCell::getUdEdge(udEdgeIndex)
                        ->getUdEdgeFromVar()
                        ->getVName(),
                    SMTCell::getUdEdge(udEdgeIndex)
                        ->getUdEdgeToVar()
                        ->getVName());
                if (!SMTCell::ifAssigned(variable_name)) {
                  tmp_var_F.push_back(variable_name);
                  SMTCell::setVar(variable_name, 2);
                  cnt_var_F++;
                }
              }
            }

            for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
                 vEdgeIndex++) {
              int toCol =
                  SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
              if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
                      pin_idx_source ||
                  SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
                      pin_idx_sink) {
                if (toCol > col || toCol < col) {
                  variable_name = fmt::format(
                      "M_{}_{}",
                      SMTCell::getVirtualEdge(vEdgeIndex)
                          ->getVCoord()
                          ->getVName(),
                      SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
                  if (!SMTCell::ifAssigned(variable_name)) {
                    tmp_var_F.push_back(variable_name);
                    SMTCell::setVar(variable_name, 2);
                    cnt_var_F++;
                  }
                }
              }
            }

            if (cnt_var_T > 0 || cnt_var_F > 0) {
              // OFFSET FLAG
              if (col - tmp_pin_idx_source * SMTCell::getMetalPitch(1) > 0 &&
                  col - tmp_pin_idx_sink * SMTCell::getMetalPitch(1) > 0) {
                SMTCell::writeConstraint(fmt::format(
                    "(assert (ite (and (= x{} (_ bv{} {})) (= x{} "
                    "(_ bv{} {})) (= y{} (_ bv{} {})) (= y{} (_ bv{} {})))",
                    source_inst_idx,
                    SMTCell::get_h_metal_col_idx(
                        metal,
                        (col - tmp_pin_idx_source * SMTCell::getMetalPitch(1))),
                    SMTCell::getBitLength_numTrackV(), sink_inst_idx,
                    SMTCell::get_h_metal_col_idx(
                        metal,
                        (col - tmp_pin_idx_sink * SMTCell::getMetalPitch(1))),
                    SMTCell::getBitLength_numTrackV(), source_inst_idx,
                    SMTCell::get_mos_placeable_row_by_site_idx(
                        site_idx, SMTCell::ifInstPMOS(source_inst_idx)),
                    SMTCell::getBitLength_numPTrackH(), sink_inst_idx,
                    SMTCell::get_mos_placeable_row_by_site_idx(
                        site_idx, SMTCell::ifInstPMOS(sink_inst_idx)),
                    SMTCell::getBitLength_numPTrackH()));
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
                SMTCell::writeConstraint(" (and");
                bool ifPMOS_passthrough = false;
                if (order_clip == "NPPN") {
                  ifPMOS_passthrough = true;
                } else if (order_clip == "PNNP") {
                  ifPMOS_passthrough = false;
                }
                int pt_row_from =
                    SMTCell::get_mos_pin_row_by_site_idx(0, ifPMOS_passthrough);
                int pt_row_to =
                    SMTCell::get_mos_pin_row_by_site_idx(1, ifPMOS_passthrough);
                for (std::size_t m = 0; m < tmp_var_T.size(); m++) {
                  // avoid setting the pass through variable to true
                  if (tmp_var_T[m].rfind(fmt::format("r{}", pt_row_from)) !=
                          std::string::npos &&
                      tmp_var_T[m].rfind(fmt::format("r{}", pt_row_to)) !=
                          std::string::npos) {
                    continue;
                  }
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} true)", tmp_var_T[m]));
                  SMTCell::cnt("l", 1);
                }

                for (std::size_t m = 0; m < tmp_var_F.size(); m++) {
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} false)", tmp_var_F[m]));
                  SMTCell::cnt("l", 1);
                }

                SMTCell::writeConstraint(") (= 1 1)))\n");
                SMTCell::cnt("c", 1);
              }
            }
          }
        }
      }
    }
  }
}

void Placement::init_placement_SD_pin(std::string order_clip) {
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    SMTCell::writeConstraint(fmt::format(";[SITE {}] Set Initial Value for S/D "
                                         "Pins of P/N FET in the same column\n",
                                         site_idx));
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string tmp_vname = "";
        // inst pin idx
        std::string pin_idx_source =
            SMTCell::getNet(netIndex)->getSource_ofNet();
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);

        // external net should NOT be considered
        if (pin_idx_source == Pin::keySON || pin_idx_sink == Pin::keySON) {
          continue;
        }

        // ignore startIdx and endIdx, not used
        std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);

        // external net should NOT be considered
        if (source_pin->getInstID() == "ext" ||
            sink_pin->getInstID() == "ext") {
          continue;
        }

        // ## Source MaxFlow Indicator
        int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
        // ## Sink MaxFlow Indicator
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        // finger
        std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(source_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());

        // ## Skip If Source/Sink TR is in the same region
        if ((source_inst_idx <= SMTCell::getLastIdxPMOS() &&
             sink_inst_idx <= SMTCell::getLastIdxPMOS()) ||
            (source_inst_idx > SMTCell::getLastIdxPMOS() &&
             sink_inst_idx > SMTCell::getLastIdxPMOS())) {
          continue;
        }

        // AGR FLAG: placement only consider metal 1
        int metal = 1;
        int row_source = SMTCell::get_mos_pin_row_by_site_idx(
            site_idx, SMTCell::ifInstPMOS(source_inst_idx));
        int row_sink = SMTCell::get_mos_pin_row_by_site_idx(
            site_idx, SMTCell::ifInstPMOS(sink_inst_idx));

        // ## Skip if Source/Sink Pin is not "Gate" Pin
        if (source_pin->getPinType() == Pin::GATE ||
            sink_pin->getPinType() == Pin::GATE) {
          continue;
        }

        int tmp_pin_idx_source = std::stoi(std::regex_replace(
            pin_idx_source, std::regex("pin\\S+_(\\d+)"), "$1"));
        int tmp_pin_idx_sink = std::stoi(std::regex_replace(
            pin_idx_sink, std::regex("pin\\S+_(\\d+)"), "$1"));

        for (int col_idx = 0;
             col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1; col_idx++) {
          // retrieve col
          int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);

          int len = SMTCell::getBitLength_numTrackV();
          std::string tmp_str = "";
          std::vector<std::string> tmp_var_T;
          std::vector<std::string> tmp_var_F;
          int cnt_var_T = 0;
          int cnt_var_F = 0;

          Triplet vCoord;
          if (SMTCell::ifSDCol_AGR(metal, col)) {
            // # Variables to Set True
            // Source
            vCoord = Triplet(1, row_source, col);
            std::string variable_name = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex, vCoord.getVName(), pin_idx_source);
            tmp_var_T.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            cnt_var_T++;

            vCoord = {}; // reset

            // Sink
            vCoord = Triplet(1, row_sink, col);
            variable_name = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex, vCoord.getVName(), pin_idx_sink);
            tmp_var_T.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            cnt_var_T++;

            // for (int row = 0; row <= SMTCell::getNumTrackH() - 4; row++) {
            // AGR FLAG
            // for (int row_idx = 0;
            //      row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3;
            //      row_idx++) {
            for (auto row_idx_it = SMTCell::pmos_routing_rows_begin(site_idx);
                 row_idx_it != SMTCell::pmos_routing_rows_end(site_idx);
                 ++row_idx_it) {
              int row_idx = *row_idx_it;
              int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
              Triplet vCoordFront = Triplet(metal, row, col);
              Triplet vCoordBack = Triplet(
                  metal, SMTCell::get_h_metal_row_by_idx(metal, row_idx + 1),
                  col);
              variable_name = fmt::format(
                  "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  commodityIndex, vCoordFront.getVName(),
                  vCoordBack.getVName());
              tmp_var_T.push_back(variable_name);
              SMTCell::setVar(variable_name, 2);
              cnt_var_T++;
            }

            // # Variables to Set False
            for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
                 udEdgeIndex++) {
              int fromCol =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->col_;
              int toCol =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
              int fromMetal =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
              int toMetal =
                  SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
              if (!(fromMetal == 1 && toMetal == 1 && fromCol == toCol &&
                    fromCol == col)) {
                variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex,
                    SMTCell::getUdEdge(udEdgeIndex)
                        ->getUdEdgeFromVar()
                        ->getVName(),
                    SMTCell::getUdEdge(udEdgeIndex)
                        ->getUdEdgeToVar()
                        ->getVName());
                if (!SMTCell::ifAssigned(variable_name)) {
                  tmp_var_F.push_back(variable_name);
                  SMTCell::setVar(variable_name, 2);
                  cnt_var_F++;
                }
              }
            }

            for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
                 vEdgeIndex++) {
              int toCol =
                  SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
              if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
                      pin_idx_source ||
                  SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
                      pin_idx_sink) {
                if (toCol > col || toCol < col) {
                  variable_name = fmt::format(
                      "M_{}_{}",
                      SMTCell::getVirtualEdge(vEdgeIndex)
                          ->getVCoord()
                          ->getVName(),
                      SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
                  if (!SMTCell::ifAssigned(variable_name)) {
                    tmp_var_F.push_back(variable_name);
                    SMTCell::setVar(variable_name, 2);
                    cnt_var_F++;
                  }
                }
              }
            }

            if (cnt_var_T > 0 || cnt_var_F > 0) {
              // OFFSET FLAG
              if (col - tmp_pin_idx_source * SMTCell::getMetalPitch(1) > 0 &&
                  col - tmp_pin_idx_sink * SMTCell::getMetalPitch(1) > 0) {
                // LISD FLAG: align by flipping, specify the flip status to make
                // sure other pins do not need to be aligned
                // set both x and y
                SMTCell::writeConstraint(fmt::format(
                    "(assert (ite (and (= x{} (_ bv{} {})) (= x{} "
                    "(_ bv{} {})) (= y{} (_ bv{} {})) (= y{} (_ bv{} {})) (= "
                    "ff{} false) (= ff{} false))",
                    source_inst_idx,
                    SMTCell::get_h_metal_col_idx(
                        metal,
                        (col - tmp_pin_idx_source * SMTCell::getMetalPitch(1))),
                    len, sink_inst_idx,
                    SMTCell::get_h_metal_col_idx(
                        metal,
                        (col - tmp_pin_idx_sink * SMTCell::getMetalPitch(1))),
                    len, source_inst_idx,
                    SMTCell::get_mos_placeable_row_by_site_idx(
                        site_idx, SMTCell::ifInstPMOS(source_inst_idx)),
                    SMTCell::getBitLength_numPTrackH(), sink_inst_idx,
                    SMTCell::get_mos_placeable_row_by_site_idx(
                        site_idx, SMTCell::ifInstPMOS(sink_inst_idx)),
                    SMTCell::getBitLength_numPTrackH(), source_inst_idx,
                    sink_inst_idx));
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
                SMTCell::writeConstraint(" (and");

                SMTCell::writeConstraint(fmt::format(
                    " (= lisd_s{}m1c{} true)", site_idx, col)); // LISD FLAG
                bool ifPMOS_passthrough = false;
                if (order_clip == "NPPN") {
                  ifPMOS_passthrough = true;
                } else if (order_clip == "PNNP") {
                  ifPMOS_passthrough = false;
                }
                int pt_row_from =
                    SMTCell::get_mos_pin_row_by_site_idx(0, ifPMOS_passthrough);
                int pt_row_to =
                    SMTCell::get_mos_pin_row_by_site_idx(1, ifPMOS_passthrough);
                for (std::size_t m = 0; m < tmp_var_T.size(); m++) {
                  // avoid setting the pass through variable to true
                  if (tmp_var_T[m].rfind(fmt::format("r{}", pt_row_from)) !=
                          std::string::npos &&
                      tmp_var_T[m].rfind(fmt::format("r{}", pt_row_to)) !=
                          std::string::npos) {
                    continue;
                  }
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} true)", tmp_var_T[m]));
                  SMTCell::cnt("l", 1);
                }

                for (std::size_t m = 0; m < tmp_var_F.size(); m++) {
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} false)", tmp_var_F[m]));
                  SMTCell::cnt("l", 1);
                }

                SMTCell::writeConstraint(") (= 1 1)))\n");
                SMTCell::cnt("c", 1);
              }
            }
          }
        }
      }
    }
  }
}

void Placement::init_inst_partition(int Partition_Parameter) {
  SMTCell::sortInstPartition();
  int prev_group_p = -1;
  int prev_group_n = -1;

  std::vector<int> tmp_p_array;
  std::vector<int> tmp_n_array;

  int minWidth_p = 0;
  int minWidth_n = 0;
  int ifRemain_p = 0;
  int ifRemain_n = 0;

  for (int i = 0; i < SMTCell::getInstPartitionCnt(); i++) {
    // if PMOS
    if (SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)) <=
        SMTCell::getLastIdxPMOS()) {
      // flush prev group
      if (prev_group_p != -1 &&
          prev_group_p != SMTCell::getInstPartitionGroup(i)) {
        // initialize an vector with h_inst_idx in it
        // sort tmp_p_array in ascending order
        std::sort(tmp_p_array.begin(), tmp_p_array.end());
        SMTCell::addInstPartitionPMOS(prev_group_p, tmp_p_array, minWidth_p);
        // clear tmp_p_array
        tmp_p_array.clear();
        minWidth_p = 0;
      }
      prev_group_p = SMTCell::getInstPartitionGroup(i);
      tmp_p_array.push_back(
          SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)));

      ifRemain_p = 1;

      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(
              SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)))
              ->getInstWidth(),
          SMTCell::getTrackEachPRow());
      minWidth_p += 2 * tmp_finger[0];

      // print previous group
      // fmt::print(" {} ", SMTCell::getInstPartitionName(i));
    } else {
      // if NMOS
      // flush prev group
      if (prev_group_n != -1 &&
          prev_group_n != SMTCell::getInstPartitionGroup(i)) {
        // initialize an vector with h_inst_idx in it
        // sort tmp_n_array in ascending order
        std::sort(tmp_p_array.begin(), tmp_p_array.end());
        SMTCell::addInstPartitionNMOS(prev_group_n, tmp_n_array, minWidth_n);
        // clear tmp_p_array
        tmp_n_array.clear();
        minWidth_n = 0;
      }
      prev_group_n = SMTCell::getInstPartitionGroup(i);
      tmp_n_array.push_back(
          SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)));
      ifRemain_n = 1;

      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(
              SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)))
              ->getInstWidth(),
          SMTCell::getTrackEachPRow());

      minWidth_n += 2 * tmp_finger[0];
    }
  }

  if (ifRemain_p == 1) {
    SMTCell::addInstPartitionPMOS(prev_group_p, tmp_p_array, minWidth_p);
  }

  if (ifRemain_n == 1) {
    SMTCell::addInstPartitionNMOS(prev_group_n, tmp_n_array, minWidth_n);
  }
};

// WARN FLAG: Align with 2F4T and 3F5T
void Placement::write_partition_constraint(int Partition_Parameter) {
  SMTCell::writeConstraint(";NOT IMPLEMENTED\n");
  if (Partition_Parameter == 2) {
    SMTCell::writeConstraint(";Set Partition Constraints\n");
    // # Lower Group => Right Side
    for (int i = 0; i < SMTCell::getPInstPartitionCnt() - 1; i++) {
      // PMOS
      int j = i + 1;
      for (int k = 0; k < SMTCell::getPInstPartitionInstIndicesCnt(i); k++) {
        for (int l = 0; l < SMTCell::getPInstPartitionInstIndicesCnt(j); l++) {
          SMTCell::writeConstraint(
              fmt::format("(assert (bvsgt x{} x{}))\n",
                          SMTCell::getPInstPartitionInstIdx(i, k),
                          SMTCell::getPInstPartitionInstIdx(j, l)));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }

    // # Upper Group => Left Side
    for (int i = 0; i < SMTCell::getNInstPartitionCnt() - 1; i++) {
      // NMOS
      int j = i + 1;
      for (int k = 0; k < SMTCell::getNInstPartitionInstIndicesCnt(i); k++) {
        for (int l = 0; l < SMTCell::getNInstPartitionInstIndicesCnt(j); l++) {
          SMTCell::writeConstraint(
              fmt::format("(assert (bvsgt x{} x{}))\n",
                          SMTCell::getNInstPartitionInstIdx(i, k),
                          SMTCell::getNInstPartitionInstIdx(j, l)));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }
    SMTCell::writeConstraint(";End of Partition Constraints\n");
  }

  if (Partition_Parameter == 1) {
    SMTCell::writeConstraint(";Set Relative Condition for Transistors whose "
                             "Gate Pins should be in the same column\n");
    std::vector<int> arr_out_p;
    std::vector<int> arr_in_p;
    std::vector<int> arr_out_n;
    std::vector<int> arr_in_n;
    std::map<int, int> h_outins;
    std::map<int, int> h_totins;

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
          if (h_outins.find(source_inst_idx) == h_outins.end()) {
            if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_out_p.push_back(source_inst_idx);
              fmt::print("Output Instance PMOS x{}\n", source_inst_idx);
            } else {
              arr_out_n.push_back(source_inst_idx);
              fmt::print("Output Instance NMOS x{}\n", source_inst_idx);
            }
            h_outins[source_inst_idx] = 1;
          }
        }
      }

      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
            if (h_outins.find(sink_inst_idx) == h_outins.end()) {
              if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
                arr_out_p.push_back(sink_inst_idx);
                fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
              } else {
                arr_out_n.push_back(sink_inst_idx);
                fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
              }
              h_outins[sink_inst_idx] = 1;
            }
          }
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (h_outins.find(source_inst_idx) == h_outins.end() &&
            h_totins.find(source_inst_idx) == h_totins.end()) {
          if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
            arr_in_p.push_back(source_inst_idx);
            fmt::print("Input Instance PMOS x{}\n", source_inst_idx);
          } else {
            arr_in_n.push_back(source_inst_idx);
            fmt::print("Input Instance NMOS x{}\n", source_inst_idx);
          }
          h_totins[source_inst_idx] = 1;
        }
      }
      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (h_outins.find(sink_inst_idx) == h_outins.end() &&
              h_totins.find(sink_inst_idx) == h_totins.end()) {
            if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_in_p.push_back(sink_inst_idx);
              fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
            } else {
              arr_in_n.push_back(sink_inst_idx);
              fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
            }
            h_totins[sink_inst_idx] = 1;
          }
        }
      }
    }

    int numOutP = arr_out_p.size();
    int numOutN = arr_out_n.size();
    int numInP = arr_in_p.size();
    int numInN = arr_in_n.size();

    if (numOutP > 0 && numInP > 0) {
      for (int i = 0; i < numOutP; i++) {
        for (int j = 0; j < numInP; j++) {
          SMTCell::writeConstraint(fmt::format("(assert (bvsgt x{} x{}))\n",
                                               arr_out_p[i], arr_in_p[j]));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }

    if (numOutN > 0 && numInN > 0) {
      for (int i = 0; i < numOutN; i++) {
        for (int j = 0; j < numInN; j++) {
          SMTCell::writeConstraint(fmt::format("(assert (bvsgt x{} x{}))\n",
                                               arr_out_n[i], arr_in_n[j]));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      std::vector<std::pair<int, int>> arr_sink;
      std::map<int, int> h_instidx;
      std::map<int, int> h_instpair;
      std::string tmp_str = "";
      int cnt_pair = 0;

      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      int width_source = tmp_finger_source[0] * 2 + 1;

      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        // ## Sink MaxFlow Indicator
        if (SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex) ==
            SMTCell::getKeySON()) {
          continue;
        }

        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        int width_sink = tmp_finger_sink[0] * 2 + 1;

        // ## Skip If Source/Sink TR is in the same region
        if (source_inst_idx <= SMTCell::getLastIdxPMOS() &&
            sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
          continue;
        }

        if (source_inst_idx > SMTCell::getLastIdxPMOS() &&
            sink_inst_idx > SMTCell::getLastIdxPMOS()) {
          continue;
        }

        // ## Skip if Source/Sink Pin is not "Gate" Pin
        if (source_pin->getPinType() != "G" && sink_pin->getPinType() != "G") {
          continue;
        }

        // ## Skip if Source/Sink Pin are the same
        if (source_inst_idx == sink_inst_idx) {
          continue;
        }

        if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
          arr_sink.push_back(std::make_pair(sink_inst_idx, width_sink));
          h_instidx[sink_inst_idx] = 1;
        }
      }

      std::vector<std::pair<int, int>> arr_p;
      std::vector<std::pair<int, int>> arr_n;
      h_instidx.clear();

      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        // ## Sink MaxFlow Indicator
        if (SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex) ==
            SMTCell::getKeySON()) {
          continue;
        }

        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        int width_sink = tmp_finger_sink[0] * 2 + 1;

        if (source_inst_idx == sink_inst_idx) {
          continue;
        }

        if (sink_pin->getPinType() == "G") {
          if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
            // PMOS
            if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
              arr_p.push_back(std::make_pair(sink_inst_idx, width_sink));
              h_instidx[sink_inst_idx] = 1;
            }
          } else {
            // NMOS
            if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
              arr_n.push_back(std::make_pair(sink_inst_idx, width_sink));
              h_instidx[sink_inst_idx] = 1;
            }
          }
        }
      }

      // int numP = arr_p.size();
      // int numN = arr_n.size();
      int numS = arr_sink.size();

      if (numS > 0 && h_outins.find(source_inst_idx) == h_outins.end()) {
        SMTCell::writeConstraint("(assert (or");

        for (int i = 0; i < numS; i++) {
          int len = SMTCell::getBitLength_numTrackV();
          // fmt::print("Gate to Gate : Inst/Width[{}/{}] [{}/{}]\n",
          //            source_inst_idx, width_source, arr_sink[i].first,
          //            arr_sink[i].second);
          if (width_source == arr_sink[i].second) {
            SMTCell::writeConstraint(fmt::format(
                " (= x{} x{})", source_inst_idx, arr_sink[i].first));
            if (width_source > 3) {
              for (int k = 0; k <= ((width_source - 1) / 2 - 1); k++) {
                SMTCell::writeConstraint(fmt::format(
                    " (= x{} (bvadd x{} (_ bv{} {})))", source_inst_idx,
                    arr_sink[i].first,
                    (2 * (k + 1)) * SMTCell::getMetalPitch(1), len));

                SMTCell::writeConstraint(fmt::format(
                    " (= x{} (bvadd x{} (_ bv{} {})))", arr_sink[i].first,
                    source_inst_idx, (2 * (k + 1)) * SMTCell::getMetalPitch(1),
                    len));
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
              }
            }

            if (h_instpair.find(source_inst_idx) == h_instpair.end()) {
              cnt_pair++;
              h_instpair[source_inst_idx] = 1;
            }
          } else if (width_source > arr_sink[i].second) {
            SMTCell::writeConstraint(fmt::format(
                " (= x{} x{})", source_inst_idx, arr_sink[i].first));
            SMTCell::writeConstraint(fmt::format(
                " (= x{} (bvadd x{} (_ bv{} {})))", arr_sink[i].first,
                source_inst_idx,
                (width_source - arr_sink[i].second) * SMTCell::getMetalPitch(1),
                len));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);

            if (h_instpair.find(source_inst_idx) == h_instpair.end()) {
              cnt_pair++;
              h_instpair[source_inst_idx] = 1;
            }
          } else {
            SMTCell::writeConstraint(fmt::format(
                " (= x{} x{})", source_inst_idx, arr_sink[i].first));
            SMTCell::writeConstraint(fmt::format(
                " (= x{} (bvadd x{} (_ bv{} {})))", source_inst_idx,
                arr_sink[i].first,
                (arr_sink[i].second - width_source) * SMTCell::getMetalPitch(1),
                len));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);

            if (h_instpair.find(source_inst_idx) == h_instpair.end()) {
              cnt_pair++;
              h_instpair[source_inst_idx] = 1;
            }
          }
        }
        SMTCell::writeConstraint("))\n");
        SMTCell::cnt("c", 0);
      }
    }

    SMTCell::writeConstraint(
        ";set relative position constraints for transistors which share the "
        "same net information\n");

    int def_offset =
        int((SMTCell::getCellWidth() / SMTCell::getMetalPitch(1)) / 1.7);

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      std::vector<std::pair<int, int>> arr_inst;
      std::map<int, int> h_instidx;
      std::map<int, int> h_instpair;
      // int cnt_pair = 0;
      int width_p = 0;
      int width_n = 0;
      int isExtNet = 0;

      // ## Source MaxFlow Indicator
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());
      int width_source = tmp_finger_source[0] * 2 + 1;

      if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
        if (h_instidx.find(source_inst_idx) == h_instidx.end()) {
          arr_inst.push_back(std::make_pair(source_inst_idx, width_source));
          h_instidx[source_inst_idx] = 1;
          width_p += width_source;
        }
      } else {
        if (h_instidx.find(source_inst_idx) == h_instidx.end()) {
          arr_inst.push_back(std::make_pair(source_inst_idx, width_source));
          h_instidx[source_inst_idx] = 1;
          width_n += width_source;
        }
      }

      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {

        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        int width_sink = tmp_finger_sink[0] * 2 + 1;

        if (source_inst_idx == sink_inst_idx) {
          continue;
        }

        if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
          if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
            arr_inst.push_back(std::make_pair(sink_inst_idx, width_sink));
            h_instidx[sink_inst_idx] = 1;
            width_p += width_sink;
          }
        } else {
          if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
            arr_inst.push_back(std::make_pair(sink_inst_idx, width_sink));
            h_instidx[sink_inst_idx] = 1;
            width_n += width_sink;
          }
        }
      }

      int numInst = arr_inst.size();
      int pos_offset = 0;
      if (width_p > width_n && width_p > def_offset) {
        pos_offset = width_p;
      } else if (width_n > width_p && width_n > def_offset) {
        pos_offset = width_n;
      } else {
        pos_offset = def_offset;
      }

      if (isExtNet == 1 && numInst > 0) {
        for (int i = 0; i < numInst; i++) {
          for (int j = i + 1; j < numInst; j++) {
            int len = SMTCell::getBitLength_numTrackV();
            fmt::print("Relative Position : Inst/Width[{}/{}][{}/{}]\n",
                       arr_inst[i].first, arr_inst[i].second, arr_inst[j].first,
                       arr_inst[j].second);

            SMTCell::writeConstraint(" (assert (or ");
            if ((arr_inst[i].first <= SMTCell::getLastIdxPMOS() &&
                 arr_inst[j].first > SMTCell::getLastIdxPMOS()) ||
                (arr_inst[i].first > SMTCell::getLastIdxPMOS() &&
                 arr_inst[j].first <= SMTCell::getLastIdxPMOS())) {
              SMTCell::writeConstraint(fmt::format(
                  " (= x{} x{})", arr_inst[i].first, arr_inst[j].first));
            }

            SMTCell::writeConstraint(fmt::format(
                " (and (bvsgt x{} x{}) (bvsle x{} (bvadd x{} (_ bv{} {}))))",
                arr_inst[i].first, arr_inst[j].first, arr_inst[i].first,
                arr_inst[j].first, pos_offset * SMTCell::getMetalPitch(1),
                len));
            SMTCell::writeConstraint(fmt::format(
                " (and (bvslt x{} x{}) (bvsle x{} (bvadd x{} (_ bv{} {}))))",
                arr_inst[i].first, arr_inst[j].first, arr_inst[j].first,
                arr_inst[i].first, pos_offset * SMTCell::getMetalPitch(1),
                len));
            SMTCell::writeConstraint("))\n");
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("c", 0);
          }
        }
      }
    }
  }
}

void Placement::write_cost_func_mos(FILE *fp) {
  for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
    fmt::print(fp, "(assert (bvsle COST_SIZE_P_SITE{} (_ bv{} {})))\n",
               site_idx, SMTCell::getNumTrackV(),
               SMTCell::getBitLength_numTrackV());
    fmt::print(fp, "(assert (bvsle COST_SIZE_N_SITE{} (_ bv{} {})))\n",
               site_idx, SMTCell::getNumTrackV(),
               SMTCell::getBitLength_numTrackV());
  }
}

// WARN FLAG: Align with 2F4T and 3F5T
void Placement::write_cost_func(FILE *fp, int Partition_Parameter) {
  int isPRT_P = 0;
  int isPRT_N = 0;
  if (Partition_Parameter == 2) {
    // PMOS
    int numP = SMTCell::getPInstPartitionCnt();
    if (numP > 0) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        int numInstP = SMTCell::getPInstPartitionInstIndicesCnt(0);
        fmt::print(fp, "(assert (= COST_SIZE_P_SITE{}", site_idx);
        for (int j = 0; j <= numInstP - 2; j++) {
          fmt::print(fp, " (max");
        }
        int i = SMTCell::getPInstPartitionInstIdx(0, 0);
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        // std::string s_first =
        //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        // fmt::print(fp, " (bvadd x{} {})", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) (bvadd "
                   "x{} (_ bv{} {}))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
        for (int j = 1; j <= numInstP - 1; j++) {
          i = SMTCell::getPInstPartitionInstIdx(0, j);
          tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // len_finger =
          //     (bmp::msb(2 * tmp_finger[0] + 1) + 1) *
          //     SMTCell::getMetalPitch(1);
          // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}))", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {})))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, "))\n");
        isPRT_P = 1;
      }
    }
    // NMOS
    int numN = SMTCell::getNInstPartitionCnt();
    if (numN > 0) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        int numInstN = SMTCell::getNInstPartitionInstIndicesCnt(0);
        fmt::print(fp, "(assert (= COST_SIZE_N_SITE{}", site_idx);
        for (int j = 0; j <= numInstN - 2; j++) {
          fmt::print(fp, " (max");
        }
        // int i = arr_bound[0];
        int i = SMTCell::getNInstPartitionInstIdx(0, 0);
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        // int len = SMTCell::getBitLength_numTrackV();
        // int len_finger =
        //     (bmp::msb(2 * tmp_finger[0] + 1) + 1) *
        //     SMTCell::getMetalPitch(1);
        // std::string s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0],
        // len); fmt::print(fp, " (bvadd x{} {})", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) (bvadd "
                   "x{} (_ bv{} {}))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
        for (int j = 1; j <= numInstN - 1; j++) {
          // i = arr_bound[j];
          i = SMTCell::getNInstPartitionInstIdx(0, j);
          tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // len_finger = (bmp::msb(2 * tmp_finger[0] + 1) + 1);
          // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}))", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {})))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, "))\n");
        isPRT_N = 1;
      }
    }
  } else if (Partition_Parameter == 1) {
    std::vector<int> arr_out_p;
    std::vector<int> arr_in_p;
    std::vector<int> arr_out_n;
    std::vector<int> arr_in_n;
    std::map<int, int> h_outins;
    std::map<int, int> h_totins;

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
          if (h_outins.find(source_inst_idx) == h_outins.end()) {
            if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_out_p.push_back(source_inst_idx);
              fmt::print("Output Instance PMOS x{}\n", source_inst_idx);
            } else {
              arr_out_n.push_back(source_inst_idx);
              fmt::print("Output Instance NMOS x{}\n", source_inst_idx);
            }
            h_outins[source_inst_idx] = 1;
          }
        }
      }

      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
            if (h_outins.find(sink_inst_idx) == h_outins.end()) {
              if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
                arr_out_p.push_back(sink_inst_idx);
                fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
              } else {
                arr_out_n.push_back(sink_inst_idx);
                fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
              }
              h_outins[sink_inst_idx] = 1;
            }
          }
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pin_idx_source = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::shared_ptr<Pin> source_pin = SMTCell::getPin(pin_idx_source);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (h_outins.find(source_inst_idx) == h_outins.end() &&
            h_totins.find(source_inst_idx) == h_totins.end()) {
          if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
            arr_in_p.push_back(source_inst_idx);
            fmt::print("Input Instance PMOS x{}\n", source_inst_idx);
          } else {
            arr_in_n.push_back(source_inst_idx);
            fmt::print("Input Instance NMOS x{}\n", source_inst_idx);
          }
          h_totins[source_inst_idx] = 1;
        }
      }
      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pin_idx_sink =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        std::shared_ptr<Pin> sink_pin = SMTCell::getPin(pin_idx_sink);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (h_outins.find(sink_inst_idx) == h_outins.end() &&
              h_totins.find(sink_inst_idx) == h_totins.end()) {
            if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_in_p.push_back(sink_inst_idx);
              fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
            } else {
              arr_in_n.push_back(sink_inst_idx);
              fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
            }
            h_totins[sink_inst_idx] = 1;
          }
        }
      }
    }

    int numOutP = arr_out_p.size();
    int numOutN = arr_out_n.size();

    if (numOutP > 1) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        fmt::print(fp, "(assert (= COST_SIZE_P_SITE{}", site_idx);
        for (int j = 0; j <= numOutP - 2; j++) {
          fmt::print(fp, " (max");
        }
        int i = arr_out_p[0];

        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        // int len = SMTCell::getBitLength_numTrackV();
        // std::string s_first =
        //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        // fmt::print(fp, " (bvadd x{} {}", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                   "(bvadd x{} (_ bv{} {}))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
        for (int j = 1; j <= numOutP - 1; j++) {
          i = arr_out_p[j];
          tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {}))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, ")))\n");
        isPRT_P = 1;
      }
    } else if (numOutP == 1) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        fmt::print(fp, "(assert (= COST_SIZE_P_SITE{}", site_idx);
        for (int j = 0; j <= numOutP - 1; j++) {
          int i = arr_out_p[j];
          std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // std::string s_first =
          //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {}))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, "))\n");
        isPRT_P = 1;
      }
    }

    if (numOutN > 1) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        fmt::print(fp, "(assert (= COST_SIZE_N_SITE{}", site_idx);
        for (int j = 0; j <= numOutN - 2; j++) {
          fmt::print(fp, " (max");
        }
        int i = arr_out_n[0];
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        // int len = SMTCell::getBitLength_numTrackV();
        // std::string s_first =
        //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        // fmt::print(fp, " (bvadd x{} {}", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                   "(bvadd x{} (_ bv{} {}))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());

        for (int j = 1; j <= numOutN - 1; j++) {
          i = arr_out_n[j];
          // tmp_finger = SMTCell::getAvailableNumFinger(
          //     SMTCell::getInst(i)->getInstWidth(),
          //     SMTCell::getTrackEachPRow());
          // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {}))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, ")))\n");
        isPRT_N = 1;
      }
    } else if (numOutN == 1) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        fmt::print(fp, "(assert (= COST_SIZE_N_SITE{}", site_idx);
        for (int j = 0; j <= numOutN - 1; j++) {
          int i = arr_out_n[j];
          std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // int len = SMTCell::getBitLength_numTrackV();
          // std::string s_first =
          //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {}))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, "))\n");
        isPRT_N = 1;
      }
    }

    if (isPRT_P == 0) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        fmt::print(fp, "(assert (= COST_SIZE_P_SITE{}", site_idx);
        for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
          fmt::print(fp, " (max");
        }
        int i = 0;
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        // int len = SMTCell::getBitLength_numTrackV();
        // std::string s_first =
        //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        // fmt::print(fp, " (bvadd x{} {}", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                   "(bvadd x{} (_ bv{} {}))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
        for (int j = 1; j <= SMTCell::getLastIdxPMOS(); j++) {
          i = j;
          tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {}))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, ")))\n");
      }
    }

    if (isPRT_N == 0) {
      for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
        fmt::print(fp, "(assert (= COST_SIZE_N_SITE{}", site_idx);
        for (int j = SMTCell::getLastIdxPMOS() + 1;
             j <= SMTCell::getNumInstance() - 2; j++) {
          fmt::print(fp, " (max");
        }
        int i = SMTCell::getLastIdxPMOS() + 1;
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        // int len = SMTCell::getBitLength_numTrackV();
        // int len_finger =
        //     (bmp::msb(2 * tmp_finger[0] + 1) + 1) *
        //     SMTCell::getMetalPitch(1);
        // std::string s_first =
        //     fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                   "(bvadd x{} (_ bv{} {}))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
        // fmt::print(fp, " (bvadd x{} {}", i, s_first);
        for (int j = SMTCell::getLastIdxPMOS() + 2;
             j <= SMTCell::getNumInstance() - 1; j++) {
          i = j;
          tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
          // len_finger =
          //     (bmp::msb(2 * tmp_finger[0] + 1) + 1) *
          //     SMTCell::getMetalPitch(1);
          // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
          // fmt::print(fp, " (bvadd x{} {}", i, s_first);
          fmt::print(fp,
                     "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                     "(bvadd x{} (_ bv{} {}))) ",
                     i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                     SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                     SMTCell::getBitLength_numTrackV(), i, 0,
                     SMTCell::getBitLength_numTrackV());
        }
        fmt::print(fp, ")))\n");
      }
    }
  } else {
    // PMOS
    for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
      fmt::print(fp, "(assert (= COST_SIZE_P_SITE{}", site_idx);
      for (int j = 0; j <= SMTCell::getLastIdxPMOS() - 1; j++) {
        fmt::print(fp, " (max");
      }
      int i = 0;
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLength_numTrackV();
      int len_finger = (bmp::msb(2 * tmp_finger[0] + 1) + 1);
      std::string tmp_str;
      if (len > 1) {
        for (int i = 0; i < len - len_finger - 1; i++) {
          tmp_str += "0";
        }
      }
      // std::string s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0],
      // len); fmt::print(fp, " (bvadd x{} {})", i, s_first);
      fmt::print(fp,
                 "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) (bvadd "
                 "x{} (_ bv{} {}))) ",
                 i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                 SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                 SMTCell::getBitLength_numTrackV(), i, 0,
                 SMTCell::getBitLength_numTrackV());

      for (int j = 1; j <= SMTCell::getLastIdxPMOS(); j++) {
        i = j;
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger = (bmp::msb(2 * tmp_finger[0] + 1) + 1);
        std::string tmp_str;
        if (len > 1) {
          for (int i = 0; i < len - len_finger - 1; i++) {
            tmp_str += "0";
          }
        }
        // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        // fmt::print(fp, " (bvadd x{} {}))", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                   "(bvadd x{} (_ bv{} {})))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 1),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
      }
      fmt::print(fp, "))\n");
    }
    // NMOS
    for (int site_idx = 0; site_idx < SMTCell::getNumSite(); site_idx++) {
      fmt::print(fp, "(assert (= COST_SIZE_N_SITE{}", site_idx);
      for (int j = SMTCell::getLastIdxPMOS() + 1;
           j <= SMTCell::getNumInstance() - 2; j++) {
        fmt::print(fp, " (max");
      }
      int i = SMTCell::getLastIdxPMOS() + 1;
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLength_numTrackV();
      int len_finger = (bmp::msb(2 * tmp_finger[0] + 1) + 1);
      std::string tmp_str = "";

      if (len > 1) {
        for (int i = 0; i < len - len_finger - 1; i++) {
          tmp_str += "0";
        }
      }
      // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
      // fmt::print(fp, " (bvadd x{} {})", i, s_first);
      fmt::print(fp,
                 "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) (bvadd "
                 "x{} (_ bv{} {}))) ",
                 i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                 SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                 SMTCell::getBitLength_numTrackV(), i, 0,
                 SMTCell::getBitLength_numTrackV());

      for (int j = SMTCell::getLastIdxPMOS() + 2;
           j <= SMTCell::getNumInstance() - 1; j++) {
        i = j;
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger = (bmp::msb(2 * tmp_finger[0] + 1) + 1);
        std::string tmp_str;

        if (len > 1) {
          for (int i = 0; i < len - len_finger - 1; i++) {
            tmp_str += "0";
          }
        }
        // s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        // fmt::print(fp, " (bvadd x{} {}))", i, s_first);
        fmt::print(fp,
                   "(ite (= y{} (_ bv{} {})) (bvadd x{} (_ bv{} {})) "
                   "(bvadd x{} (_ bv{} {})))) ",
                   i, SMTCell::get_mos_placeable_row_by_site_idx(site_idx, 0),
                   SMTCell::getBitLength_numPTrackH(), i, 2 * tmp_finger[0],
                   SMTCell::getBitLength_numTrackV(), i, 0,
                   SMTCell::getBitLength_numTrackV());
      }
      fmt::print(fp, "))\n");
    }
  }
}

void Placement::write_top_metal_track_usage(FILE *fp) {
  // top metal track usage
  if (SMTCell::getNumMetalLayer() == 4) {
    int metal = 4; // AGR FLAG: toMetal = 4; M3 and M4 has the same row
    for (int row_idx = 0; row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3;
         row_idx++) {
      // retrieve row/col
      int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
      fmt::print(fp, "(assert (= M4_TRACK_{} (or", row_idx);
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        // int fromMetal =
        //     SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
        // int fromCol =
        // SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->col_; int toCol
        // = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
        int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->row_;
        int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->row_;
        if (toMetal == 4 && (fromRow == row && toRow == row)) {
          std::string variable_name =
              fmt::format("M_{}_{}", SMTCell::getUdEdgeFromVarName(udEdgeIndex),
                          SMTCell::getUdEdgeToVarName(udEdgeIndex));
          if (SMTCell::ifVar(variable_name)) {
            fmt::print(fp, " {}", variable_name);
          }
        }
      }

      fmt::print(fp, ")))\n");
    }

    for (auto en : SMTCell::getExtNet()) {
      int netIndex = SMTCell::getNetIdx(std::to_string(en.first));
      for (int row_idx = 0;
           row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
        std::string tmp_str = "";
        int cnt_var = 0;
        // retrieve row/col
        int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
        tmp_str +=
            fmt::format("(assert (= N{}_M4_TRACK_{} (or", en.first, row_idx);
        for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
             udEdgeIndex++) {
          int toMetal =
              SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
          int fromRow =
              SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->row_;
          int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->row_;
          if (toMetal == 4 && (fromRow == row && toRow == row)) {
            for (int commodityIndex = 0;
                 commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
                 commodityIndex++) {
              std::string variable_name =
                  fmt::format("N{}_C{}_E_{}_{}", en.first, commodityIndex,
                              SMTCell::getUdEdge(udEdgeIndex)
                                  ->getUdEdgeFromVar()
                                  ->getVName(),
                              SMTCell::getUdEdge(udEdgeIndex)
                                  ->getUdEdgeToVar()
                                  ->getVName());
              // fmt::print("{}\n", variable_name);
              if (SMTCell::ifVar(variable_name)) {
                // fmt::print("FLAG5\n");
                tmp_str += fmt::format(" {}", variable_name);
                cnt_var++;
              }
            }
          }
        }

        tmp_str += ")))\n";
        if (cnt_var == 0) {
          tmp_str = fmt::format("(assert (= N{}_M4_TRACK_{} false))\n",
                                en.first, row_idx);
        }
        fmt::print(fp, tmp_str);
      }

      fmt::print(fp, "(assert (= N{}_M4_TRACK (or", en.first);
      for (int row_idx = 0;
           row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
        // int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
        fmt::print(fp, " N{}_M4_TRACK_{}", en.first, row_idx);
      }
      fmt::print(fp, ")))\n");
    }
  }
}

void Placement::write_instance_alignment(FILE *fp) {
  fmt::print(fp, ";Align instance as much as possible\n");
  for (int pmos_idx = 0; pmos_idx < SMTCell::getLastIdxPMOS() + 1; pmos_idx++) {
    fmt::print(fp, "(assert (or ");
    for (int nmos_idx = SMTCell::getLastIdxPMOS() + 1;
         nmos_idx < SMTCell::getInstCnt(); nmos_idx++) {
      fmt::print(fp, "(= x{} x{})", pmos_idx, nmos_idx);
    }
    fmt::print(fp, "))\n");
  }
  for (int nmos_idx = SMTCell::getLastIdxPMOS() + 1;
       nmos_idx < SMTCell::getInstCnt(); nmos_idx++) {
    fmt::print(fp, "(assert (or ");
    for (int pmos_idx = 0; pmos_idx < SMTCell::getLastIdxPMOS() + 1;
         pmos_idx++) {
      fmt::print(fp, "(= x{} x{})", nmos_idx, pmos_idx);
    }
    fmt::print(fp, "))\n");
  }
}

void Placement::write_bound_horizontal_track_width(FILE *fp) {
  fmt::print(
      fp, "; Binding M0 routing to max column (avoid out-of-bound routing)\n");
  // fmt::print(fp, "(minimize (CELL_WIDTH (=");
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
    // skip vertical metal
    if (SMTCell::ifVertMetal(metal)) {
      continue;
    }
    // start from the second column to avoid trivial case
    for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      fmt::print(fp, "(assert (= M{}_COLEND_{} ", metal, col_idx);
      int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
      int cpp_amount = ceil((double)col / SMTCell::getMetalPitch(1));
      // fmt::print(" [INFO] col {} M1P {} CPP Amount: {}\n", col,
      // SMTCell::getMetalPitch(1), cpp_amount); if any of the GR_V is true,
      // then the cell width is the current column
      fmt::print(fp, " (ite (or");
      for (int row_idx = 0;
           row_idx <= SMTCell::get_h_metal_numTrackH(metal) - 3; row_idx++) {
        // retrieve row/col
        int row = SMTCell::get_h_metal_row_by_idx(metal, row_idx);
        std::string variable_name =
            fmt::format("GR_V_m{}r{}c{}", metal, row, col); // GR_V_0_0
        fmt::print(fp, " {}", variable_name);
      }
      fmt::print(fp, ") (_ bv{} {})", cpp_amount,
                 SMTCell::getBitLength_numTrackV());
      fmt::print(fp, " (_ bv0 {}))))\n", SMTCell::getBitLength_numTrackV());
    }
    // fmt::print(fp, ")))\n");
  }
  fmt::print(fp, "; Binding M0 routing to total cell width (avoid out-of-bound "
                 "routing)\n");
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
    // skip vertical metal
    if (SMTCell::ifVertMetal(metal)) {
      continue;
    }
    fmt::print(fp, "(assert (= M{}_CELL_WIDTH ", metal);
    // start from the second column to avoid trivial case
    std::vector<std::string> tmp_str;
    for (int col_idx = 1; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      // add the column to the vector
      tmp_str.push_back(fmt::format("M{}_COLEND_{}", metal, col_idx));
    }
    std::string tmp_max_str = FormatHelper::write_multi_max(tmp_str);
    fmt::print(fp, " {}))\n", tmp_max_str);
    // fmt::print(fp, ")))\n");
  }
  fmt::print(fp, "; Minimize Cell Width\n");
  // define the total cell width
  if (SMTCell::getNumMetalLayer() == 4) {
    fmt::print(fp, "(assert (= TOTAL_CELL_WIDTH (max");
    for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
      // skip vertical metal
      if (SMTCell::ifVertMetal(metal)) {
        continue;
      }
      fmt::print(fp, " M{}_CELL_WIDTH", metal);
    }
    fmt::print(fp, ")))\n");
  } else {
    fmt::print(fp, "(assert (= TOTAL_CELL_WIDTH M2_CELL_WIDTH))\n");
  }

  // minimize the cell width
  // fmt::print(fp, "(minimize TOTAL_CELL_WIDTH)\n");
  fmt::print(fp, "(assert (bvsle TOTAL_CELL_WIDTH COST_SIZE))\n");
}

// WARN FLAG: Align with 2F4T and 3F5T
void Placement::write_minimize_cost_func(FILE *fp, int Partition_Parameter,
                                         bool ifMinimizeM4) {
  int idx_obj = 0;
  int limit_obj = 150;

  if (SMTCell::getNumMetalLayer() == 4) {
    limit_obj = 150;
    // limit_obj = 50;
  } else {
    limit_obj = 50;
  }

  int num_netOpt = SMTCell::getNetOptCnt();

  if (Partition_Parameter == 2 && num_netOpt > 0) {
    std::string str_opt;
    str_opt = "(minimize (bvadd";
    idx_obj = 0;
    // set it already, no need to set it again
    // if (SMTCell::getNumTrack() == 4) {
    //   limit_obj = 150;
    // } else {
    //   limit_obj = 50;
    // }
    fmt::print(fp, str_opt);

    int metal = 3;
    for (int col_idx = 0; col_idx <= SMTCell::get_h_metal_numTrackV(metal) - 1;
         col_idx++) {
      // retrieve col
      // int col = SMTCell::get_h_metal_col_by_idx(metal, col_idx);
      if (idx_obj >= limit_obj) {
        idx_obj = 0;
        fmt::print(fp, "))\n");
        fmt::print(fp, "(minimize (bvadd");
      }
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
        // int fromCol =
        // SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->col_; int toCol
        // = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->col_;
        if (fromMetal == toMetal && toMetal == 4) {
          // same as foreach my $key(keys %h_net_opt)
          for (int i = 0; i < num_netOpt; i++) {
            std::string variable_name = fmt::format(
                "E_{}_{}",
                SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
                SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
            if (SMTCell::ifVar(variable_name)) {
              fmt::print(fp, " (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                         variable_name,
                         SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                         SMTCell::getBitLength_numTrackV(),
                         SMTCell::getBitLength_numTrackV());
              idx_obj++;
            }
          }
        }
      }
    }
    fmt::print(fp, "))\n");
    idx_obj = 0;
  }

  /* Experimental turning off for now */
  if (SMTCell::getNumMetalLayer() == 4 && ifMinimizeM4 == true) {
    fmt::print(fp, "; Minimize Top Track Utilization\n");
    idx_obj = 0;
    limit_obj = 10;
    fmt::print(fp, "(minimize (bvadd");
    for (int row_idx = 0; row_idx <= SMTCell::getNumTrackH() - 3; row_idx++) {
      if (idx_obj >= limit_obj) {
        idx_obj = 0;
        fmt::print(fp, "))\n");
        fmt::print(fp, "(minimize (bvadd");
      }
      fmt::print(fp, " (ite (= M4_TRACK_{} true) (_ bv1 {}) (_ bv0 {}))",
                 row_idx, SMTCell::getBitLength_numTrackV(),
                 SMTCell::getBitLength_numTrackV());
      idx_obj++;
    }
    fmt::print(fp, "))\n");
  }

  idx_obj = 0;
  if (SMTCell::getNumTrack() == 4 || SMTCell::getNumTrack() == 3 ||
      SMTCell::getNumTrack() == 2) {
    limit_obj = 150;
  } else {
    limit_obj = 50;
  }

  fmt::print(fp, "; Minimize Wirelength\n");
  std::string tmp_str_obj;
  // minimize for M3 to M4 and M4 to M4
  if (ifMinimizeM4) {
    fmt::print(fp, "; 1. Minimize for M3 to M4 and M4 to M4\n");
    idx_obj = 0;
    tmp_str_obj.clear();
    for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
         udEdgeIndex++) {
      if (idx_obj >= limit_obj) {
        idx_obj = 0;
        fmt::print(fp, "(minimize (bvadd");
        fmt::print(fp, tmp_str_obj.c_str());
        fmt::print(fp, "))\n");
        tmp_str_obj.clear();
      }
      int fromMetal =
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
      int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
      // if (fromMetal == toMetal && (toMetal >= 2 && toMetal <= 3)) {
      // LISD FLAG: disregard anything for M2
      if ((fromMetal == 4 && toMetal == 4) ||
          (fromMetal == 3 && toMetal == 4)) {
        std::string variable_name = fmt::format(
            "M_{}_{}",
            SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
        if (SMTCell::ifVar(variable_name)) {
          tmp_str_obj += fmt::format(
              " (ite (= {} true) (_ bv{} {}) (_ bv0 {}))", variable_name,
              SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
              SMTCell::getBitLength_numTrackV(),
              SMTCell::getBitLength_numTrackV());
          idx_obj++;
        }
      }
    }
    if (tmp_str_obj.size() > 0) {
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
    }
  }
  fmt::print(fp, "; 3. Minimize for M3 to M3\n");
  // minimize for M2 to M2 and M3 to M3
  idx_obj = 0;
  tmp_str_obj.clear();
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    // if (fromMetal == toMetal && (toMetal >= 2 && toMetal <= 3)) {
    // LISD FLAG: disregard anything for M2
    if (fromMetal == toMetal && (toMetal == 3)) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                                   SMTCell::getBitLength_numTrackV(),
                                   SMTCell::getBitLength_numTrackV());
        idx_obj++;
      }
    }
  }
  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  // minimize for M3 to M4 and M4 to M4
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    // int fromMetal =
    // SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    if (toMetal == 4) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                                   SMTCell::getBitLength_numTrackV(),
                                   SMTCell::getBitLength_numTrackV());
        idx_obj++;
      }
    }
  }
  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  fmt::print(fp, "; 2. Minimize for M1 to M2 (via) and M2 to M3 (via)\n");
  // minimize for M1 to M2 (via) and M2 to M3 (via)
  idx_obj = 0;
  tmp_str_obj.clear();
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    if (fromMetal != toMetal && (toMetal <= 3 && toMetal >= 2)) {
      // LISD FLAG: disregard anything for M2
      // if (fromMetal != toMetal && (toMetal == 3)) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                                   SMTCell::getBitLength_numTrackV(),
                                   SMTCell::getBitLength_numTrackV());
        idx_obj++;
      }
    }
  }
  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  fmt::print(fp, "; 4. Minimize for M2 to M2 (metal)\n");
  // minimize for M1 to M2 (via) and M2 to M3 (via)
  idx_obj = 0;
  tmp_str_obj.clear();
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    if (fromMetal == toMetal && toMetal == 2) {
      // LISD FLAG: disregard anything for M2
      // if (fromMetal != toMetal && (toMetal == 3)) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                                   SMTCell::getBitLength_numTrackV(),
                                   SMTCell::getBitLength_numTrackV());
        idx_obj++;
      }
    }
  }
  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }
  // Ignored the case $MM_Parameter < 4 because it never happens in our
  // formulation
}

void Placement::write_minimize_via_cost(FILE *fp) {
  int idx_obj = 0;
  int limit_obj = 150;

  if (SMTCell::getNumMetalLayer() == 4) {
    limit_obj = 150;
    // limit_obj = 50;
  } else {
    limit_obj = 50;
  }

  fmt::print(fp, "; Minimize Via Cost\n");
  std::string tmp_str_obj;
  fmt::print(fp, "; 1. Minimize for M3 to M4 Via\n");
  // minimize for M2 to M2 and M3 to M3
  idx_obj = 0;
  tmp_str_obj.clear();
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    // if (fromMetal == toMetal && (toMetal >= 2 && toMetal <= 3)) {
    // LISD FLAG: disregard anything for M2
    if (toMetal == 4 && fromMetal == 3) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                                   SMTCell::getBitLength_numTrackV(),
                                   SMTCell::getBitLength_numTrackV());
        idx_obj++;
      }
    }
  }
  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  fmt::print(fp, "; 2. Minimize for M1 to M2 (via) and M2 to M3 (via)\n");
  // minimize for M1 to M2 (via) and M2 to M3 (via)
  idx_obj = 0;
  tmp_str_obj.clear();
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->metal_;
    if (fromMetal != toMetal && (toMetal <= 3 && toMetal >= 2)) {
      // LISD FLAG: disregard anything for M2
      // if (fromMetal != toMetal && (toMetal == 3)) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeFromVar()->getVName(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdEdgeToVar()->getVName());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} {}) (_ bv0 {}))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost(),
                                   SMTCell::getBitLength_numTrackV(),
                                   SMTCell::getBitLength_numTrackV());
        idx_obj++;
      }
    }
  }
  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }
}