#define FMT_HEADER_ONLY
#include "dbConfig.hpp"
#include <fmt/core.h>
#include <fmt/format.h>

dbConfig::dbConfig(const std::string &config_path, std::string infile) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();
  // Architecture
  // ALLOW_LISD_EXTENSIBLE_ = config["ALLOW_LISD_EXTENSIBLE"]["value"];
  MIN_GATE_CUT_Parameter_ = config["MIN_GATE_CUT_Parameter"]["value"];
  // AVOID_GCUT_ON_DUMMY_ = config["AVOID_GCUT_ON_DUMMY"]["value"];
  // AVOID_CB_IN_MIDDLE_ROW_ = config["AVOID_CB_IN_MIDDLE_ROW"]["value"];
  GATE_PASSTHROUGH_ = config["GATE_PASSTHROUGH"]["value"];
  SD_PASSTHROUGH_ = config["SD_PASSTHROUGH"]["value"];
  // parse into variables
  Z3Seed_ = config["z3_seed"]["value"];
  EEQ_Parameter_ = config["EEQ_Parameter"]["value"];
  // MultiHeight
  MultiHeight_Parameter_ = config["MH_Parameter"]["value"];
  // Design Rule Parameters
  MAR_M1_Parameter_ = config["MAR_M1_Parameter"]["value"];
  MAR_M2_Parameter_ = config["MAR_M2_Parameter"]["value"];
  MAR_M3_Parameter_ = config["MAR_M3_Parameter"]["value"];
  MAR_M4_Parameter_ = config["MAR_M4_Parameter"]["value"];
  EOL_M1_B_ADJ_Parameter_ = config["EOL_M1_B_ADJ_Parameter"]["value"];
  EOL_M1_B_Parameter_ = config["EOL_M1_B_Parameter"]["value"];
  EOL_M2_R_ADJ_Parameter_ = config["EOL_M2_R_ADJ_Parameter"]["value"];
  EOL_M2_R_Parameter_ = config["EOL_M2_R_Parameter"]["value"];
  EOL_M3_B_ADJ_Parameter_ = config["EOL_M3_B_ADJ_Parameter"]["value"];
  EOL_M3_B_Parameter_ = config["EOL_M3_B_Parameter"]["value"];
  EOL_M4_R_ADJ_Parameter_ = config["EOL_M4_R_ADJ_Parameter"]["value"];
  EOL_M4_R_Parameter_ = config["EOL_M4_R_Parameter"]["value"];
  VR_M1M2_Parameter_ = config["VR_M1M2_Parameter"]["value"];
  VR_M2M3_Parameter_ = config["VR_M2M3_Parameter"]["value"];
  VR_M3M4_Parameter_ = config["VR_M3M4_Parameter"]["value"];
  PRL_M1_Parameter_ = config["PRL_M1_Parameter"]["value"];
  PRL_M2_Parameter_ = config["PRL_M2_Parameter"]["value"];
  PRL_M3_Parameter_ = config["PRL_M3_Parameter"]["value"];
  PRL_M4_Parameter_ = config["PRL_M4_Parameter"]["value"];
  SHR_M1_Parameter_ = config["SHR_M1_Parameter"]["value"];
  SHR_M2_Parameter_ = config["SHR_M2_Parameter"]["value"];
  SHR_M3_Parameter_ = config["SHR_M3_Parameter"]["value"];
  SHR_M4_Parameter_ = config["SHR_M4_Parameter"]["value"];
  // Minimum Pin Opening
  M1_MPO_Parameter_ = config["M1_MPO_Parameter"]["value"];
  // Complexity Reduction : Placement or Partitioning
  Partition_Parameter_ = config["Partition_Parameter"]["value"];
  Placement_Parameter_ = config["Placement_Parameter"]["value"];
  // Hidden Parameters
  M0_MPO_Parameter_ = 4;
  BoundaryCondition_ = 0;
  SON_ = 1;
  DoublePowerRail_ = 0;
  MM_Parameter_ = 4;
  EXT_Parameter_ = 0;
  BCP_Parameter_ = 1;
  XOL_Mode_ = 0;
  NDE_Parameter_ = 1;
  ML_Parameter_ = 5;
  Local_Parameter_ = 0;
  tolerance_Parameter_ = 3;
  BS_Parameter_ = 1;
  objpart_Parameter_ = 0;
  XOL_Parameter_ = 2;
  PE_Parameter_ = 0;
  PE_Mode_ = 1;
  M1_Separation_Parameter_ = 1;
  // Special Condition for DFF cells
  if (infile.find("DFF") != std::string::npos ||
      infile.find("SDFFQ") != std::string::npos) {
    Partition_Parameter_ = 2;
    BCP_Parameter_ = 1;
    NDE_Parameter_ = 0;
    BS_Parameter_ = 0;
    fmt::print("\na     [INFO] DFF Cell Detected. Forcing the following "
               "constraint ... ***");
    fmt::print(
        "\na     [INFO] \tDisable NDE, BS; Partitioning = 2; BCP = 1; ***");
  } else if (Partition_Parameter_ == 2) {
    fmt::print("\n    [INFO] Partitioning = 2; BCP = 1; NDE_Parameter = 0; BS_Parameter = 0***");
    BCP_Parameter_ = 1;
    NDE_Parameter_ = 0;
    BS_Parameter_ = 0;
  }
  if (MultiHeight_Parameter_ == 1) {
    fmt::print("\na     [INFO] MultiHeight Mode Enabled. Turning off Breaking "
               "Symmetry and Localization\n");
    BS_Parameter_ = 0;
    NDE_Parameter_ = 1;
    Local_Parameter_ = 1;
  }

  dbConfig::checkParameter();
}

void dbConfig::printParameter() {
  fmt::print("a     ===== General Parameters =====\n");
  fmt::print("a        Z3 Seed = {}\
                \n",
             Z3Seed_);
  fmt::print("a        EEQ Parameter = {}\
                \n",
             EEQ_Parameter_);
  fmt::print("a        MultiHeight Parameter = {}\
                \n",
             MultiHeight_Parameter_);
  fmt::print("a     ===== Design Rule Parameters =====\n");
  fmt::print("a        Minimum Area Rules : [MAR_M1 = {}, MAR_M2 = {}, "
             "MAR_M3 = {}, MAR_M4 = {}]\n",
             MAR_M1_Parameter_, MAR_M2_Parameter_, MAR_M3_Parameter_,
             MAR_M4_Parameter_);
  // [EOL Design Rule]
  fmt::print(
      "a        End-Of-Line Rules : [EOL_M1_B_Adj = {}, EOL_M1_B = {},\n",
      EOL_M1_B_ADJ_Parameter_, EOL_M1_B_Parameter_);
  fmt::print(
      "a                          : [EOL_M2_R_Adj = {}, EOL_M2_R = {},\n",
      EOL_M2_R_ADJ_Parameter_, EOL_M2_R_Parameter_);
  fmt::print(
      "a                          : [EOL_M3_B_Adj = {}, EOL_M3_B = {},\n",
      EOL_M3_B_ADJ_Parameter_, EOL_M3_B_Parameter_);
  fmt::print(
      "a                          : [EOL_M4_R_Adj = {}, EOL_M4_R = {},\n",
      EOL_M4_R_ADJ_Parameter_, EOL_M4_R_Parameter_);
  // [VR Design Rule]
  fmt::print("a        Via-to-Via Rules  : [VR_M1M2 = {}, VR_M2M3 = {}, "
             "VR_M3M4 = {}]\n",
             VR_M1M2_Parameter_, VR_M2M3_Parameter_, VR_M3M4_Parameter_);
  // [PRL Design Rule]
  fmt::print("a        Parallel Run Length Rules : [PRL_M1 = {}, PRL_M2 = {}, "
             "PRL_M3 = {}, PRL_M4 = {}]\n",
             PRL_M1_Parameter_, PRL_M2_Parameter_, PRL_M3_Parameter_,
             PRL_M4_Parameter_);
  // [SHR Design Rule]
  fmt::print("a        Spacing to Hierarchy Rules : [SHR_M1 = {}, SHR_M2 = {}, "
             "SHR_M3 = {}, SHR_M4 = {}]\n",
             SHR_M1_Parameter_, SHR_M2_Parameter_, SHR_M3_Parameter_,
             SHR_M4_Parameter_);
  fmt::print(
      "a        Parameter Options : [MPO = {}], [Localization = {} (T{})]\n",
      M1_MPO_Parameter_, Local_Parameter_, tolerance_Parameter_);
  fmt::print("a	                        [Cell Partitioning = {}], [Diffusion Height Sharing "
             "= {}], [Breaking Symmetry = {}]\n",
             Partition_Parameter_, (NDE_Parameter_ == 0 ? "Disable" : "Enable"),
             BS_Parameter_);
  fmt::print("a	                        [DBMode = {}({})], [Objective "
             "Partitioning = {}]\n\n",
             XOL_Mode_, XOL_Parameter_, objpart_Parameter_);
}

void dbConfig::checkParameter() {
  if (MIN_GATE_CUT_Parameter_ == 0) {
    // std::cout << "\na     *** Disable Gate Cut ***";
    fmt::print("\na     [WARNING] Disable Gate Cut ***");
  };
  if (MAR_M1_Parameter_ == 0) {
    // std::cout << "\na     *** Disable MAR_M1 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable MAR_M1 (When Parameter == 0) ***");
  }
  if (MAR_M2_Parameter_ == 0) {
    // std::cout << "\na     *** Disable MAR_M2 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable MAR_M2 (When Parameter == 0) ***");
  }
  if (MAR_M3_Parameter_ == 0) {
    // std::cout << "\na     *** Disable MAR_M3 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable MAR_M3 (When Parameter == 0) ***");
  }
  if (MAR_M4_Parameter_ == 0) {
    // std::cout << "\na     *** Disable MAR_M4 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable MAR_M4 (When Parameter == 0) ***");
  }
  if (EOL_M1_B_ADJ_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M1_B_ADJ (When Parameter == 0)
    // ***";
    fmt::print(
        "\na     [WARNING] Disable EOL_M1_B_ADJ (When Parameter == 0) ***");
  }
  if (EOL_M1_B_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M1_B (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable EOL_M1_B (When Parameter == 0) ***");
  }
  if (EOL_M2_R_ADJ_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M2_R_ADJ (When Parameter == 0)
    // ***";
    fmt::print(
        "\na     [WARNING] Disable EOL_M2_R_ADJ (When Parameter == 0) ***");
  }
  if (EOL_M2_R_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M2_R (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable EOL_M2_R (When Parameter == 0) ***");
  }
  if (EOL_M3_B_ADJ_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M3_B_ADJ (When Parameter == 0)
    // ***";
    fmt::print(
        "\na     [WARNING] Disable EOL_M3_B_ADJ (When Parameter == 0) ***");
  }
  if (EOL_M3_B_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M3_B (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable EOL_M3_B (When Parameter == 0) ***");
  }
  if (EOL_M4_R_ADJ_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M4_R_ADJ (When Parameter == 0)
    // ***";
    fmt::print(
        "\na     [WARNING] Disable EOL_M4_R_ADJ (When Parameter == 0) ***");
  }
  if (EOL_M4_R_Parameter_ == 0) {
    // std::cout << "\na     *** Disable EOL_M4_R (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable EOL_M4_R (When Parameter == 0) ***");
  }
  if (VR_M1M2_Parameter_ == 0) {
    // std::cout << "\na     *** Disable VR_M1M2 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable VR_M1M2 (When Parameter == 0) ***");
  }
  if (VR_M2M3_Parameter_ == 0) {
    // std::cout << "\na     *** Disable VR_M2M3 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable VR_M2M3 (When Parameter == 0) ***");
  }
  if (VR_M3M4_Parameter_ == 0) {
    // std::cout << "\na     *** Disable VR_M3M4 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable VR_M3M4 (When Parameter == 0) ***");
  }
  if (PRL_M1_Parameter_ == 0) {
    // std::cout << "\na     *** Disable PRL_M1 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable PRL_M1 (When Parameter == 0) ***");
  }
  if (PRL_M2_Parameter_ == 0) {
    // std::cout << "\na     *** Disable PRL_M2 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable PRL_M2 (When Parameter == 0) ***");
  }
  if (PRL_M3_Parameter_ == 0) {
    // std::cout << "\na     *** Disable PRL_M3 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable PRL_M3 (When Parameter == 0) ***");
  }
  if (PRL_M4_Parameter_ == 0) {
    // std::cout << "\na     *** Disable PRL_M4 (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable PRL_M4 (When Parameter == 0) ***");
  }
  if (SHR_M1_Parameter_ < 2) {
    // std::cout << "\na     *** Disable SHR_M1 (When Parameter <= 1) ***";
    fmt::print("\na     [WARNING] Disable SHR_M1 (When Parameter <= 1) ***");
  }
  if (SHR_M2_Parameter_ < 2) {
    // std::cout << "\na     *** Disable SHR_M2 (When Parameter <= 1) ***";
    fmt::print("\na     [WARNING] Disable SHR_M2 (When Parameter <= 1) ***");
  }
  if (SHR_M3_Parameter_ < 2) {
    // std::cout << "\na     *** Disable SHR_M3 (When Parameter <= 1) ***";
    fmt::print("\na     [WARNING] Disable SHR_M3 (When Parameter <= 1) ***");
  }
  if (SHR_M4_Parameter_ < 2) {
    // std::cout << "\na     *** Disable SHR_M4 (When Parameter <= 1) ***";
    fmt::print("\na     [WARNING] Disable SHR_M4 (When Parameter <= 1) ***");
  }
  if (Local_Parameter_ == 0) {
    // std::cout << "\na     *** Disable Localization (When Parameter == 0)
    // ***";
    fmt::print(
        "\na     [WARNING] Disable Localization (When Parameter == 0) ***");
  }
  if (Partition_Parameter_ == 0) {
    // std::cout << "\na     *** Disable Cell Partitioning (When Parameter == 0)
    // ***";
    fmt::print("\na     [WARNING] Disable Cell Partitioning (When Parameter == "
               "0) ***");
  }
  if (Placement_Parameter_ == 0) {
    // std::cout << "\na     *** Disable Cell Placement (When Parameter == 0)
    // ***";
    fmt::print(
        "\na     [WARNING] Disable Cell Placement (When Parameter == 0) ***");
  }
  if (objpart_Parameter_ == 0) {
    std::cout
        // << "\na     *** Disable Objective Partitioning (When Parameter == 0)
        // ***";
        << "\na     [WARNING] Disable Objective Partitioning (When Parameter "
           "== 0) ***";
  }
  if (BS_Parameter_ == 0) {
    // std::cout << "\na     *** Disable Breaking Symmetry (When Parameter == 0)
    // ***";
    fmt::print("\na     [WARNING] Disable Breaking Symmetry (When Parameter == "
               "0) ***");
  }
  if (NDE_Parameter_ == 0) {
    // std::cout << "\na     *** Disable FST (When Parameter == 0) ***";
    fmt::print("\na     [WARNING] Disable FST (When Parameter == 0) ***");
  }

  if (M0_MPO_Parameter_ < 2) {
    // std::cout << "[ERROR] M0_MPO_Parameter is not valid!\n";
    fmt::print("a     [ERROR] M0_MPO_Parameter is not valid!\n");
    exit(-1);
  }

  if (M1_MPO_Parameter_ < 1 || M1_MPO_Parameter_ > 4) {
    // std::cout << "[ERROR] M1_MPO_Parameter is not valid!\n";
    fmt::print("a     [ERROR] M1_MPO_Parameter is not valid!\n");
    exit(-1);
  }

  // std::cout << "\n";
  fmt::print("\n");

  if (XOL_Mode_ == 0) {
    XOL_Parameter_ = 2;
  } else {
    XOL_Parameter_ = 4;
  }
}

void dbConfig::check_Partition_Parameter(int sizeOfPartition) {
  if (Partition_Parameter_ != 0) {
    if (sizeOfPartition != 0) {
      fmt::print("a     [WARNING] Partition_Parameter is set! Disabling BS and "
                 "NDE!\n");
      NDE_Parameter_ = 0;
      BS_Parameter_ = 0;
    }
  }
}

void dbConfig::check_Placement_Parameter(int sizeOfPlacement) {
  if (Placement_Parameter_ != 0) {
    if (sizeOfPlacement != 0) {
      fmt::print("a     [WARNING] Placement_Parameter is set! Disabling BS and "
                 "NDE!\n");
      NDE_Parameter_ = 0;
      BS_Parameter_ = 0;
    }
  }
}

void dbConfig::check_Placement_and_Partition_Parameter(int sizeOfPlacement,
                                                       int sizeOfPartition) {
  if (Placement_Parameter_ != 0 && Partition_Parameter_ != 0) {
    if (sizeOfPlacement == 0 && sizeOfPartition == 0) {
      fmt::print("a     [WARNING] Placement_Parameter and Partition_Parameter "
                 "is not valid! Both sizes are 0!\n");
      Placement_Parameter_ = 0;
      Partition_Parameter_ = 0;
      NDE_Parameter_ = 1;
      BS_Parameter_ = 1;
      fmt::print("a     [WARNING] Enabling NDE, BS!\n");
    } else {
      fmt::print("a     [WARNING] FLAG 1 : Placement_Parameter and "
                 "Partition_Parameter is set! Disabling BS and NDE!\n");
      NDE_Parameter_ = 0;
      BS_Parameter_ = 0;
    }
  } else {
    if (sizeOfPlacement != 0 && sizeOfPartition != 0) {
      fmt::print("a     [WARNING] FLAG 2 : Placement_Parameter and "
                 "Partition_Parameter is set! Disabling BS and NDE!\n");
      NDE_Parameter_ = 0;
      BS_Parameter_ = 0;
    }
  }
}

void dbConfig::check_MH_Parameter() {
  if (MultiHeight_Parameter_ == 1) {
    fmt::print(
        "a     [WARNING] MultiHeight Enabled.\n");
    // BS_Parameter_ = 0;
    Local_Parameter_ = 1;
  }
}
