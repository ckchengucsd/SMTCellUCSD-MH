#define FMT_HEADER_ONLY
#include <algorithm>
#include <boost/algorithm/string/classification.hpp> // Include boost::for is_any_of
#include <boost/algorithm/string/split.hpp>          // Include for boost::split
#include <boost/multiprecision/integer.hpp>          // for returning bit length
#include <cmath>
#include <filesystem>
#include <fmt/core.h>
#include <fmt/format.h>
#include <fstream>
#include <iostream>
#include <map>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

#include "genSMTInput.hpp"
namespace bmp = boost::multiprecision;

int main(int argc, char *argv[]) {
  // ### Pre-processing ########################################################
  auto const workdir = std::filesystem::current_path();
  std::string result_path = "";
  std::string pinlayout_path = "";
  std::string config_path = "";

  dbConfig *config;
  SMTCell *smtcell = new SMTCell();

  if (argc != 4) {
    std::cerr << "\n*** [ERROR] Wrong CMD";
    std::cerr << "\n   [USAGE]: ./PL_FILE [inputfile_pinLayout] "
                 "[inputfile_config] [result_dir]\n\n";
    exit(1);
  } else {
    pinlayout_path = argv[1];
    config_path = argv[2];
    result_path = argv[3];
  }

  std::filesystem::path result_dir(result_path);
  // output directory
  fmt::print("a   Working Directory: {}\n", workdir.c_str());
  fmt::print("a   Result Directory: {}\n", result_dir.c_str());
  // append workdir result_dir and logs
  auto const logdir = result_dir / "logs";
  fmt::print("a   Log Directory: {}\n", logdir.c_str());
  auto const outdir = result_dir / "inputSMT";
  fmt::print("a   Output Directory: {}\n", outdir.c_str());

  // check input files
  std::ifstream config_file(config_path);
  std::ifstream pinlayout_file(pinlayout_path);

  if (!config_file.good()) {
    fmt::print("\n*** [ERROR] FILE DOES NOT EXIST..{}\n", config_path);
    exit(1);
  } else {
    config = new dbConfig(config_path, pinlayout_path);
    smtcell->initTrackInfo(config_path);
  }

  if (!pinlayout_file.good()) {
    fmt::print("\n*** [ERROR] FILE DOES NOT EXIST..{}\n", pinlayout_path);
    exit(1);
  } else {
    fmt::print("\n");
    fmt::print("a   Version Info : 1.0 AGR Version\n");
    config->printParameter();
    fmt::print("a   Generating SMT-LIB 2.0 Standard inputfile based on the "
               "following files.\n");
    fmt::print("a     Input Layout:  {}/{}\n", workdir.c_str(), pinlayout_path);
  }

  // ### END: Pre-processing
  // ###########################################################################
  // ### ENTITY STRUCTURE
  // Output Directory Creation
  system(("mkdir -p " + outdir.string()).c_str());
  auto cellName = pinlayout_path.substr(pinlayout_path.rfind("/") + 1);
  auto outfile =
      outdir / cellName.substr(0, cellName.find("."))
                   .append(fmt::format("_{}F_{}T.smt2", SMTCell::getNumFin(),
                                       SMTCell::getNumTrack()));
  // DEBUG MODE : Output Log File
  auto designRuleLog = logdir / "debug/designRule.log";
  system(("touch " + designRuleLog.string()).c_str());
  std::FILE *dr_log = std::fopen(designRuleLog.c_str(), "w");

  auto graphLog = logdir / "debug/graph.log";
  system(("touch " + graphLog.string()).c_str());
  std::FILE *graph_log = std::fopen(graphLog.c_str(), "w");

  fmt::print("a     SMT-LIB2.0 File:    {}\n", outfile.c_str());

  smtcell->setNumMetalLayer(config->getMM_Parameter()); // M1~M4

  LayoutParser *parser = new LayoutParser();
  parser->parsePinLayout(pinlayout_path, config->getPartition_Parameter());
  delete parser;

  // check Partitioning if it is valid
  config->check_Partition_Parameter(SMTCell::getInstPartitionCnt());
  config->check_Placement_Parameter(SMTCell::getInstPlacementCnt());
  config->check_Placement_and_Partition_Parameter(
      SMTCell::getInstPlacementCnt(), SMTCell::getInstPartitionCnt());
  config->check_MH_Parameter();

  // Placement related will be handled by Placement class
  Placement *plc = new Placement();
  plc->init_inst_partition(config->getPartition_Parameter());

  // ### Remove Power Pin/Net Information from data structure
  // Remove Power Pin
  smtcell->removePowerPin();

  // Remove Power Net
  smtcell->removePowerNet();

  fmt::print("a     # Pins              = {}\n", smtcell->getPinCnt());
  fmt::print("a     # Nets              = {}\n", smtcell->getNetCnt());

  // ### END:  ENTITY STRUCTURE
  // ###########################################################################
  // ### GRAPH STRUCTURE
  Graph *graph = new Graph();

  // ### GRAPH Generation (Required before generating VERTEX)
  // Graph Generation pre-determines the "jumping distance" for each vertex
  // This ensures offset and gear ratios are calculated correctly
  graph->init_graph();
  graph->dump_graph(graph_log);

  // ### VERTEX Generation
  graph->init_vertices();
  fmt::print("a     # Vertices          = {}\n", smtcell->getVertexCnt());
  fmt::print(graph_log, "a     # Vertices          = {}\n",
             smtcell->getVertexCnt());
  // smtcell->dump_vertices();

  // ### UNDIRECTED EDGE Generation
  graph->init_udedges();
  // smtcell->dump_udEdges();
  fmt::print("a     # udEdges           = {}\n", smtcell->getUdEdgeCnt());
  fmt::print(graph_log, "a     # udEdges           = {}\n",
             smtcell->getUdEdgeCnt());

  // ### BOUNDARY VERTICES Generation.
  graph->init_boundaryVertices(config->getEXT_Parameter());
  fmt::print("a     # Boundary Vertices = {}\n",
             smtcell->getBoundaryVertexCnt());
  fmt::print(graph_log, "a     # Boundary Vertices = {}\n",
             smtcell->getBoundaryVertexCnt());
  // SMTCell::dump_boundaryVertices();

  graph->init_outerPins();
  fmt::print("a     # Outer Pins        = {}\n", smtcell->getOuterPinCnt());
  fmt::print(graph_log, "a     # Outer Pins        = {}\n",
             smtcell->getOuterPinCnt());
  // smtcell->dump_outerPins();

  graph->init_corner();
  fmt::print("a     # Left Corners      = {}\n", smtcell->getLeftCornerCnt());
  fmt::print("a     # Right Corners     = {}\n", smtcell->getRightCornerCnt());
  fmt::print("a     # Front Corners     = {}\n", smtcell->getFrontCornerCnt());
  fmt::print("a     # Back Corners      = {}\n", smtcell->getBackCornerCnt());
  fmt::print(graph_log, "a     # Left Corners      = {}\n",
             smtcell->getLeftCornerCnt());
  fmt::print(graph_log, "a     # Right Corners     = {}\n",
             smtcell->getRightCornerCnt());
  fmt::print(graph_log, "a     # Front Corners     = {}\n",
             smtcell->getFrontCornerCnt());
  fmt::print(graph_log, "a     # Back Corners      = {}\n",
             smtcell->getBackCornerCnt());

  // ### SOURCE and SINK Generation. All sources and sinks are supernodes.
  // ### DATA STRUCTURE:  SOURCE or SINK [netName] [#subNodes] [Arr. of
  // sub-nodes, i.e., vertices]
  graph->init_source(config->getSON());
  fmt::print("a     # Ext Nets          = {}\n", smtcell->getExtNetCnt());
  fmt::print("a     # Sources           = {}\n", smtcell->getSourceCnt());
  fmt::print("a     # Sinks             = {}\n", smtcell->getSinkCnt());
  fmt::print(graph_log, "a     # Ext Nets          = {}\n",
             smtcell->getExtNetCnt());
  fmt::print(graph_log, "a     # Sources           = {}\n",
             smtcell->getSourceCnt());
  fmt::print(graph_log, "a     # Sinks             = {}\n",
             smtcell->getSinkCnt());

  graph->init_pinSON(config->getSON());

  // ### VIRTUAL EDGE Generation
  graph->init_virtualEdges();
  graph->init_edgeInOut();
  graph->init_vedgeInOut();

  fmt::print("a     # Virtual Edges     = {}\n", smtcell->getVirtualEdgeCnt());
  fmt::print(graph_log, "a     # Virtual Edges     = {}\n",
             smtcell->getVirtualEdgeCnt());
  // ### END:  DATA STRUCTURE
  // ###########################################################################
  std::FILE *out = std::fopen(outfile.c_str(), "w");

  fmt::print("a   Generating SMT-LIB 2.0 Standard Input Code.\n");

  // INIT
  fmt::print(out, "; Formulation for SMT\n");
  fmt::print(out, "; Format: SMT-LIB 2.0\n");
  fmt::print(out, "; Version: SMTCell-1.0\n");
  fmt::print(
      out,
      "; Authors: Yucheng Wang, Daeyeal Lee, Dongwon Park, Chung-Kuan Cheng\n");
  fmt::print(out, "; DO NOT DISTRIBUTE IN ANY PURPOSE!\n\n");
  fmt::print(out, "; Input File:  {}/{}\n", workdir.c_str(), pinlayout_path);
  fmt::print(out, "; a        Design Rule Parameters :\n");

  // [MAR Design Rule]
  fmt::print(out,
             "; Minimum Area Rules : [MAR_M1 = {}, MAR_M2 = {}, MAR_M3 = {}, "
             "MAR_M4 = {}]\n",
             config->getMAR_M1_Parameter(), config->getMAR_M2_Parameter(),
             config->getMAR_M3_Parameter(), config->getMAR_M4_Parameter());
  // [EOL Design Rule]
  fmt::print(out, "; End-Of-Line Rules : [EOL_M1_B_Adj = {}, EOL_M1_B = {},\n",
             config->getEOL_M1_B_ADJ_Parameter(),
             config->getEOL_M1_B_Parameter());
  fmt::print(out, ";                     [EOL_M2_R_Adj = {}, EOL_M2_R = {},\n",
             config->getEOL_M2_R_ADJ_Parameter(),
             config->getEOL_M2_R_Parameter());
  fmt::print(out, ";                     [EOL_M3_B_Adj = {}, EOL_M3_B = {},\n",
             config->getEOL_M3_B_ADJ_Parameter(),
             config->getEOL_M3_B_Parameter());
  fmt::print(out, ";                     [EOL_M4_R_Adj = {}, EOL_M4_R = {},\n",
             config->getEOL_M4_R_ADJ_Parameter(),
             config->getEOL_M4_R_Parameter());
  // [VR Design Rule]
  fmt::print(
      out, "; Via-to-Via Rules  : [VR_M1M2 = {}, VR_M2M3 = {}, VR_M3M4 = {}]\n",
      config->getVR_M1M2_Parameter(), config->getVR_M2M3_Parameter(),
      config->getVR_M3M4_Parameter());
  // [PRL Design Rule]
  fmt::print(
      out,
      "; Parallel Run Length Rules : [PRL_M1 = {}, PRL_M2 = {}, PRL_M3 = "
      "{}, PRL_M4 = {}]\n",
      config->getPRL_M1_Parameter(), config->getPRL_M2_Parameter(),
      config->getPRL_M3_Parameter(), config->getPRL_M4_Parameter());
  // [SHR Design Rule]
  fmt::print(
      out,
      "; Spacing to Hierarchy Rules : [SHR_M1 = {}, SHR_M2 = {}, SHR_M3 = "
      "{}, SHR_M4 = {}]\n",
      config->getSHR_M1_Parameter(), config->getSHR_M2_Parameter(),
      config->getSHR_M3_Parameter(), config->getSHR_M4_Parameter());

  fmt::print(out,
             "; Parameter Options : [MPO = {}], [Localization = {} (T{})]\n",
             config->getM1_MPO_Parameter(), config->getLocal_Parameter(),
             config->getTolerance_Parameter());
  fmt::print(
      out, "; [Cell Partitioning = {}], [FST = {}], [Breaking Symmetry = {}]\n",
      config->getPartition_Parameter(),
      (config->getNDE_Parameter() == 0 ? "Disable" : "Enable"),
      config->getBS_Parameter());
  fmt::print(out, "; [DBMode = {}({})], [Objective Partitioning = {}]\n\n",
             config->getXOL_Mode(), config->getXOL_Parameter(),
             config->getObjpart_Parameter());

  fmt::print(out, ";Layout Information\n");
  fmt::print(out, ";	Placement\n");
  fmt::print(out, ";	# Vertical Tracks   = {}\n", smtcell->getNumPTrackV());
  fmt::print(out, ";	# Horizontal Tracks = {}\n", smtcell->getNumPTrackH());
  fmt::print(out, ";	# Instances         = {}\n", smtcell->getNumInstance());
  fmt::print(out, ";	Routing\n");
  fmt::print(out, ";	# Vertical Tracks   = {}\n", smtcell->getNumTrackV());
  fmt::print(out, ";	# Horizontal Tracks = {}\n", smtcell->getNumTrackH());
  fmt::print(out, ";	# Nets              = {}\n", smtcell->getNetCnt());
  fmt::print(out, ";	# Pins              = {}\n", smtcell->getPinCnt());
  fmt::print(out, ";	# Sources           = {}\n", smtcell->getSourceCnt());
  fmt::print(out, ";	List of Sources   = ");

  fmt::print(out, "{}", smtcell->dump_sources());
  fmt::print(out, "\n");
  fmt::print(out, ";	# Sinks             = {}\n", smtcell->getSinkCnt());
  fmt::print(out, ";	List of Sinks     = ");

  fmt::print(out, "{}", smtcell->dump_sinks());
  fmt::print(out, "\n");
  fmt::print(out, ";	# Outer Pins        = {}\n", smtcell->getOuterPinCnt());
  fmt::print(out, ";	List of Outer Pins= ");

  // All SON (Super Outer Node)
  fmt::print(out, "{}", smtcell->dump_SON());
  fmt::print(out, "\n");
  fmt::print(out, ";	Outer Pins Information= ");

  // All SON (Super Outer Node)
  fmt::print(out, "{}", smtcell->dump_SON_detail());
  fmt::print(out, "\n\n\n");

  // ### Z3 Option Set ###
  fmt::print(out, "(set-option :smt.core.minimize true)\n");
  fmt::print(out, "(set-option :smt.random_seed {})\n", config->getZ3Seed());
  // get multiple cell solutions
  if (config->getEEQ_Parameter() > 1) {
    fmt::print(out, "(set-option :opt.priority pareto)\n");
  }
  fmt::print(out, ";Begin SMT Formulation\n\n");

  // Flow related constraints will be handled by Flow Writer
  FlowWriter *flowWriter = new FlowWriter();

  // Design Rule related constraints will be handled by Design Rule Writer
  DesignRuleWriter *drWriter = new DesignRuleWriter();

  // Init COST_SIZE, M2 Track Usage Varaible
  plc->init_cost_var(out);
  SMTCell::writeCostHint(out);

  // LISD FLAG: Init Lisd Column Variable
  fmt::print("a     ===== EXP. Variables for LISD =====\n");
  plc->init_lisd_col_var(out);

  // GC FLAG: Init Gate Cut Column Variable
  fmt::print("a     ===== EXP. Variables for Gate Cut =====\n");
  plc->init_gcut_col_var(out);

  // PASS THROUGH FLAG: Init Pass-Through Column Variable
  fmt::print("a     ===== EXP. Variables for Pass-Through =====\n");
  plc->init_pass_through_col_var(out);

  // ### Placement ###
  fmt::print("a     ===== A. Variables for Placement =====\n");
  fmt::print(out, ";A. Variables for Placement\n");

  // Utility function: max
  fmt::print("a     A-0. Max Function\n");
  fmt::print(out, ";A-0. Max Function\n");
  plc->write_max_func(out);

  // Init Placement Variable: X, Y, width, flip, height, number of fingers
  fmt::print("a     A-1. Initialize Placement Variables\n");
  fmt::print(out, ";A-1. Initialize Placement Variables\n");
  plc->write_placement_var(out);

  // Fix placement from SMTLite
  fmt::print("a     Fix Placement from SMTLite{}\n", SMTCell::getPlcHint());
  if (SMTCell::getPlcHint() == true) {
    fmt::print("a     Fix Placement from SMTLite\n");
    fmt::print(out, ";Fix Placement from SMTLite\n");
    plc->fix_placement(out);
  }

  fmt::print("a     ===== B. Constraints for Placement =====\n");
  fmt::print(out, "\n");
  fmt::print(out, ";B. Constraints for Placement\n");

  // Instance Placement Range Constraint given by X
  // AGR FLAG: X should be at least the offset
  fmt::print("a     B-0. Set Placement Range\n");
  fmt::print(out, ";B-0. Set Placement Range\n");
  plc->write_placement_range_constr(out);

  // PMOS Area
  fmt::print("a     B-1. Set PMOS Placement Variables\n");
  fmt::print(out, ";B-1. Set PMOS Placement Variables\n");
  plc->set_placement_var_pmos(out);

  // NMOS Area
  fmt::print("a     B-2. Set NMOS Placement Variable\n");
  fmt::print(out, ";B-2. Set NMOS Placement Variable\n");
  plc->set_placement_var_nmos(out);

  // Force Gate to be placed on even columns, S/D otherwise
  // AGR FLAG: DISABLED. columns now are real numbers.
  fmt::print("a     B-3. Set Legal Placmenet Column\n");
  fmt::print(out, ";B-3. Set Legal Placmenet Column\n");
  plc->set_placement_legal_col(out);

  // Get the minimum width of the MOSFET
  smtcell->setMOSMinWidth();

  if (SMTCell::getPlcHint() == false) {
    fmt::print("a     B-4. Remove Symmetric X-Y Placement {}\n",
               config->getBS_Parameter());
    fmt::print(out, ";B-4. Remove Symmetric Placement \n");
    plc->remove_x_symmetric_placement(out, config->getBS_Parameter());
    plc->remove_y_symmetric_placement(out, config->getBS_Parameter());
  }
  // XOL Mode => 0: SDB, 1:DDB, 2:(Default)SDB/DDB mixed
  fmt::print("a     B-5. PMOS: SDB, DDB, Mixed SDB/DDB \n");
  fmt::print(out, ";B-5. PMOS: SDB, DDB, Mixed SDB/DDB \n");
  plc->write_XOL(out, true, config->getXOL_Parameter(),
                 config->getNDE_Parameter(), config->getXOL_Parameter());
  fmt::print("a     B-6. NMOS: SDB, DDB, Mixed SDB/DDB \n");
  fmt::print(out, ";B-6. NMOS: SDB, DDB, Mixed SDB/DDB \n");
  plc->write_XOL(out, false, config->getXOL_Parameter(),
                 config->getNDE_Parameter(), config->getXOL_Parameter());

  fmt::print(out, "\n");

  fmt::print("a     ===== C. Constraints for Placement =====\n");
  // ### Extensible Boundary variables
  // # In Extensible Case , Metal binary variables
  fmt::print("a     C-1. Initialize Extensible Variables\n");
  fmt::print(out, ";C-1. Initialize Extensible Variables\n");
  graph->init_extensible_boundary(config->getBoundaryCondition());

  // ### Commodity Flow binary variables
  fmt::print("a     C-2. Initialize Commodity Flow Variables\n");
  fmt::print(out, ";C-2. Initialize Commodity Flow Variables\n");
  flowWriter->init_commodity_flow_var();

  fmt::print("a     C-3. Localization of Intra-FET Routing\n");
  fmt::print(out, ";C-3. Localization of Intra-FET Routing\n");
  plc->localize_adjacent_pin(1);
  fmt::print(out, "\n");

  int isEnd = 0;
  int numLoop = 0;

  while (isEnd == 0) {
    if (smtcell->getCandidateAssignCnt() > 0) {
      // ## Merge Assignment Information
      smtcell->mergeAssignment();
    }

    if (numLoop == 0) {
      fmt::print("a     ===== Initial SMT Code Generation =====\n");
      fmt::print(dr_log, "a     ===== Initial SMT Code Generation =====\n");
    } else {
      fmt::print("a     ===== SMT Code Reduction Loop #{} =====\n", numLoop);
      fmt::print(dr_log, "a     ===== SMT Code Reduction Loop #{} =====\n",
                 numLoop);
    }

    smtcell->reset_var();
    smtcell->reset_cnt();

    // ### LISD FLAG: Set LISD Column Constraint
    fmt::print("a     0.0.0 LISD Column Constraint\n");
    plc->write_lisd_col_has_pin_alignment_or_empty_space();
    plc->write_lisd_col_has_only_one_connection();

    fmt::print("a     0.0.1 GCut Column Constraint\n");
    smtcell->writeConstraint(";GCut limits middle connections \n");
    plc->write_gate_cut_with_two_cb_condition();
    plc->write_prohibit_gate_connection(config->getMin_GATE_CUT_Parameter());

    // ### Pass-Through Column Constraint
    fmt::print("a     0.0.2 Pass-Through Column Constraint\n");
    smtcell->writeConstraint("; Pass-Through Column Constraint\n");
    plc->write_pass_through_col(config->getGATE_PASSTHROUGH(), config->getSD_PASSTHROUGH());
    plc->write_pass_through_col_has_gate_pin_alignment(smtcell->getOrderClip());
    plc->write_pass_through_col_has_sd_pin_alignment(smtcell->getOrderClip());

    // ### limit LISD/GCut Column by COST_SIZE
    plc->write_limit_lisd_gc_pt_var_by_cost_size();

    // ### Set Default Gate Metal according to the capacity variables
    fmt::print("a     0.1. Default G Metal\n");
    plc->set_default_G_metal();

    fmt::print("a     0.2. Unset Rightmost Metal\n");
    smtcell->writeConstraint(";Unset Rightmost Metal\n");
    plc->unset_rightmost_metal();

    // device partition constraint
    if (SMTCell::getPlcHint() == false) {
      fmt::print("a     0.4. Partition Constraint\n");
      smtcell->writeConstraint(";Partition Constraint\n");
      plc->write_partition_constraint(config->getPartition_Parameter());
    }

    fmt::print("a     0.5. G Pin Placement\n");
    smtcell->writeConstraint(";G Pin Placement\n");
    plc->init_placement_G_pin(smtcell->getOrderClip());

    fmt::print("a     0.6. SD Pin Placement\n");
    smtcell->writeConstraint(";SD Pin Placement\n");
    plc->init_placement_SD_pin(smtcell->getOrderClip());

    fmt::print("a     0.7. Flow Capacity Control\n");
    smtcell->writeConstraint(";Flow Capacity Control\n");
    flowWriter->write_flow_capacity_control();

    fmt::print("a     0.8. Localize Commodity\n");
    flowWriter->localize_commodity(config->getLocal_Parameter(),
                                   config->getTolerance_Parameter());

    // ### COMMODITY FLOW Conservation
    fmt::print("a     1. Commodity flow conservation ");
    flowWriter->write_flow_conservation(out, config->getEXT_Parameter());

    // ### Exclusiveness use of VERTEX
    // Only considers incoming flows by nature
    fmt::print("a     2. Exclusiveness use of vertex ");
    flowWriter->write_vertex_exclusive_placement_passthrough(out);
    flowWriter->write_vertex_exclusive_routing(out);

    // ### EDGE assignment
    // Assign edges based on commodity information
    fmt::print("a     3. Edge assignment ");
    flowWriter->write_edge_assignment(out);

    // ### Exclusiveness use of EDGES + Metal segment assignment
    // using edge usage information
    fmt::print("a     4. Exclusiveness use of edge ");
    flowWriter->write_edge_exclusive(out);

    // ### Geometry variables for LEFT, RIGHT, FRONT, BACK directions
    fmt::print("a     6. Geometric variables ");
    drWriter->write_geometric_variables_AGR(dr_log);

    fmt::print("a     7. Minimum area rule ");
    drWriter->write_MAR_AGR_rule(
        config->getMAR_M1_Parameter(), config->getMAR_M2_Parameter(),
        config->getMAR_M3_Parameter(), config->getMAR_M4_Parameter(),
        0, dr_log);

    fmt::print("a     8. Tip-to-Tip spacing rule ");
    drWriter->write_EOL_AGR_rule(
        config->getEOL_M1_B_ADJ_Parameter(), config->getEOL_M1_B_Parameter(),
        config->getEOL_M2_R_ADJ_Parameter(), config->getEOL_M2_R_Parameter(),
        config->getEOL_M3_B_ADJ_Parameter(), config->getEOL_M3_B_Parameter(),
        config->getEOL_M4_R_ADJ_Parameter(), config->getEOL_M4_R_Parameter(),
        0, dr_log);

    fmt::print("a     9. Via-to-via spacing rule ");
    drWriter->write_VR_AGR_rule(
        config->getVR_M1M2_Parameter(), config->getVR_M2M3_Parameter(),
        config->getVR_M3M4_Parameter(), 0, dr_log);

    fmt::print("a     10. Parallel Run Length Rule ");
    drWriter->write_PRL_AGR_rule(
        config->getPRL_M1_Parameter(), config->getPRL_M2_Parameter(),
        config->getPRL_M3_Parameter(), config->getPRL_M4_Parameter(),
        0, dr_log);

    fmt::print("a     11. Net Consistency");
    smtcell->writeConstraint(";11. Net Consistency\n");
    flowWriter->write_net_consistency();

    fmt::print("a     12. Pin Accessibility Rule ");
    smtcell->writeConstraint(";12. Pin Accessibility Rule\n");
    drWriter->write_pin_access_rule(config->getM1_MPO_Parameter(),
                                    config->getMAR_M3_Parameter(),
                                    config->getEOL_M3_B_Parameter(), dr_log);

    fmt::print("a     13. Step Height Rule ");
    drWriter->write_SHR_AGR_rule(
        config->getSHR_M1_Parameter(), config->getSHR_M2_Parameter(),
        config->getSHR_M3_Parameter(), config->getSHR_M4_Parameter(),
        0, dr_log);

    // break; // when done, comment out
    numLoop++;
    if (smtcell->getCandidateAssignCnt() == 0 ||
        config->getBCP_Parameter() == 0) {
      isEnd = 1;
    } else {
      smtcell->clear_writeout();
    }
  }

  int total_var = smtcell->getTotalVar();
  int total_clause = smtcell->getTotalClause();
  int total_literal = smtcell->getTotalLiteral();
  fmt::print("a     ===== D. Variables for Routing =====\n");
  fmt::print(out, ";===== D. Variables for Routing =====\n");
  // Writing to everything to .SMT2
  smtcell->flushVarAndConstraint(out, config->getBCP_Parameter());

  fmt::print("a     ===== E. Check SAT & Optimization =====\n");
  fmt::print(out, ";===== E. Check SAT & Optimization =====\n");

  // cost related to P/N
  fmt::print("a     E-0. Cost Function for MOSFET\n");
  fmt::print(out, ";E-0. Cost Function for MOSFET\n");
  plc->write_cost_func_mos(out);

  // top metal track usage
  fmt::print("a     E-1. Top Metal Layer Usage\n");
  fmt::print(out, ";E-1. Top Metal Layer Usage\n");
  plc->write_top_metal_track_usage(out);

  fmt::print("a     E-2. Cost Function Calculation\n");
  fmt::print(out, ";E-2. Cost Function Calculation\n");
  plc->write_cost_func(out, config->getPartition_Parameter());

  fmt::print(
      out, "(assert (= COST_SIZE (max COST_SIZE_P_SITE0 (max COST_SIZE_P_SITE1 "
           "(max COST_SIZE_N_SITE0 COST_SIZE_N_SITE1)))))\n");
  fmt::print(out, "(minimize COST_SIZE)\n");

  fmt::print("a     Minimize Wire Length\n");
  fmt::print(out, ";Minimize Wire Length\n");
  plc->write_minimize_via_cost(out);
  plc->write_minimize_cost_func(out, config->getObjpart_Parameter(), true);

  fmt::print("a     E-4. Minimize Cost Function\n");
  fmt::print(out, ";E-4. Minimize Cost Function\n");
  plc->write_bound_horizontal_track_width(out);
  plc->write_instance_alignment(out);
  /* Hard constraint: Always disable the left most column */
  for (int row_idx = 0; row_idx <= SMTCell::get_h_metal_numTrackH(2) - 3;
       row_idx++) {
    fmt::print(out, "(assert (= GL_V_m2r{}c0 false))\n", row_idx);
    fmt::print(out, "(assert (= GL_V_m2r{}c30 false))\n", row_idx);
  }
  /* Hard constraint: NAND and NOR should never use M4 layers */
  if (cellName.find("NAND") != std::string::npos ||
      cellName.find("NOR") != std::string::npos) {
    fmt::print("a     EXP2-3. Prohibit Top Track\n");
    fmt::print(out, ";EXP2-3. Prohibit Top Track\n");
    if (SMTCell::getNumMetalLayer() == 4) {
      for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
        fmt::print(out, "(assert (= M4_TRACK_{} false))\n", i);
      }
      for (auto en : SMTCell::getExtNet()) {
        for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
          fmt::print(out, "(assert (= N{}_M4_TRACK_{} false))\n", en.first, i);
        }
        fmt::print(out, "(assert (= N{}_M4_TRACK false))\n", en.first);
      }
    }
  }

  // DEBUG
  fmt::print(out, ";DEBUG\n");
  fmt::print(out, "(check-sat)\n");
  fmt::print(out, "(get-model)\n");
  fmt::print(out, "(get-objectives)\n");
  fmt::print("a      ===== Complexity Summary =====\n");
  fmt::print("a      Total # Variables      = {}\n", total_var);
  fmt::print("a      Total # Literals       = {}\n", total_literal);
  fmt::print("a      Total # Clauses        = {}\n", total_clause);
  fmt::print(out, "; Total # Variables      = {}\n", total_var);
  fmt::print(out, "; Total # Literals       = {}\n", total_literal);
  fmt::print(out, "; Total # Clauses        = {}\n", total_clause);
  // close file
  std::fclose(out);
  std::fclose(dr_log);
  std::fclose(graph_log);

  smtcell->dump_summary();

  // free memory
  cellName.clear();
  delete flowWriter;
  delete drWriter;
  delete plc;
  delete graph;
  delete config;
  delete smtcell;
}
