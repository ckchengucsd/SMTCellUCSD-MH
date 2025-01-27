#include "SMTCell.hpp"

bool SMTCell::DEBUG_MODE_ = true;

int SMTCell::debug_checkpoint_idx = 0;

std::string SMTCell::writeout = "";

// Cell Configurations (related to AGR)
int SMTCell::standardCellWidth = 0;
int SMTCell::standardCellHeight = 0;
// MultiHeight Configurations
int SMTCell::num_clip = 0;
int SMTCell::num_site = 0;
std::string SMTCell::order_clip = "PNNP";
std::map<int, int> SMTCell::num_row_per_clip = {};
std::map<int, std::vector<int>> SMTCell::mh_placement_rows = {};
std::map<int, std::vector<int>> SMTCell::mh_routing_rows = {};
std::vector<std::vector<int>> SMTCell::mh_pmos_placement_rows = {};
std::vector<std::vector<int>> SMTCell::mh_nmos_placement_rows = {};
std::vector<int> SMTCell::mh_pmos_placeable_rows = {};
std::vector<int> SMTCell::mh_nmos_placeable_rows = {};
std::vector<std::vector<int>> SMTCell::mh_pmos_routing_rows = {};
std::vector<std::vector<int>> SMTCell::mh_nmos_routing_rows = {};
std::vector<int> SMTCell::mh_pmos_pin_rows = {};
std::vector<int> SMTCell::mh_nmos_pin_rows = {};
std::vector<int> SMTCell::mh_pmos_gate_rows = {};
std::vector<int> SMTCell::mh_nmos_gate_rows = {};

// Placement vs. Routing Horizontal Track Mapping Array [Placement, Routing]
std::map<int, int> SMTCell::mapTrack = {};

// Number of Routing Contact for Each Width of FET
std::map<int, int> SMTCell::numContact = {{1, 2}, {2, 2}, {3, 2}};
std::map<int, int> SMTCell::h_mapTrack = {};
std::map<int, int> SMTCell::h_RTrack = {};
std::map<int, int> SMTCell::h_numConn = {};
std::map<int, int> SMTCell::h_MP = {{1, 60}, {2, 1}, {3, 80}, {4, 1}};
std::map<int, int> SMTCell::h_offset = {{1, 0}, {2, 0}, {3, 0}, {4, 0}};
int SMTCell::row_distance = 0;

// counting vars
int SMTCell::c_v_placement_ = 0;
int SMTCell::c_v_placement_aux_ = 0;
int SMTCell::c_v_routing_ = 0;
int SMTCell::c_v_routing_aux_ = 0;
int SMTCell::c_v_connect_ = 0;
int SMTCell::c_v_connect_aux_ = 0;
int SMTCell::c_v_dr_ = 0;
int SMTCell::c_c_placement_ = 0;
int SMTCell::c_c_routing_ = 0;
int SMTCell::c_c_connect_ = 0;
int SMTCell::c_c_dr_ = 0;
int SMTCell::c_l_placement_ = 0;
int SMTCell::c_l_routing_ = 0;
int SMTCell::c_l_connect_ = 0;
int SMTCell::c_l_dr_ = 0;

// pre-partition
int SMTCell::costHint = 0;
bool SMTCell::plcHint = false;
int SMTCell::instPlacementCnt = 0;

// Track related info
int SMTCell::numFin_ = 0;
int SMTCell::numTrack_ = 0;
int SMTCell::placementRow_ = 0;
float SMTCell::trackEachRow_ = 0.0;
int SMTCell::trackEachPRow_ = 0;
int SMTCell::numTrackH_ = 0;
int SMTCell::numTrackV_ = 0;
int SMTCell::numMetalLayer_ = 0;
int SMTCell::numPTrackH_ = 0;
int SMTCell::numPTrackV_ = 0;
int SMTCell::lastIdxPMOS_ = -1;
int SMTCell::numInstance_ = 0;
int SMTCell::numNets_org_ = 0;

// AGR related info
// store numTrackV and numTrackH for each layer
std::map<int, int> SMTCell::h_metal_numTrackV = {};
std::map<int, int> SMTCell::h_metal_numTrackH = {};

// store [METAL] ==> [ROW]
std::map<int, std::vector<int>> SMTCell::h_metal_row = {};
// store [METAL] ==> [COL]
std::map<int, std::vector<int>> SMTCell::h_metal_col = {};

// store [METAL] ==> [ROW] ==> [ROW_IDX]
std::map<int, std::map<int, int>> SMTCell::h_metal_row_idx = {};
// store [METAL] ==> [COL] ==> [COL_IDX]
std::map<int, std::map<int, int>> SMTCell::h_metal_col_idx = {};

// store all unique columns
std::vector<int> SMTCell::h_unique_col = {};

// store lisd columns
std::map<int, std::vector<int>> SMTCell::h_lisd_col = {};

// Cell related info
int SMTCell::minWidth_ = 0;

// store variable declaration and index
int SMTCell::idx_var_ = 1;
int SMTCell::idx_clause_ = 1;
std::map<std::string, int> SMTCell::h_var = {};
std::map<std::string, int> SMTCell::h_assign = {};
std::map<std::string, int> SMTCell::h_assign_new = {};

// Cell Entity related
// ### PIN variables
std::vector<std::shared_ptr<Pin>> SMTCell::pins;
std::map<unsigned int, int> SMTCell::h_InstPin_to_netID;
std::map<unsigned int, int> SMTCell::h_instID_to_pinStart;
std::map<unsigned int, int> SMTCell::h_pinName_to_idx;
std::map<unsigned int, int> SMTCell::h_outpinId_idx;
std::map<unsigned int, std::string> SMTCell::h_pin_net;

// ### NET variables
std::vector<std::shared_ptr<Net>> SMTCell::nets;
std::map<int, int> SMTCell::h_extnets;
std::map<unsigned int, int> SMTCell::h_netId_to_netIdx;
std::map<unsigned int, int> SMTCell::h_outnets;

// ### INSTANCE variables
std::vector<Instance *> SMTCell::insts;
std::map<unsigned int, int> SMTCell::h_inst_idx;

// ### Partition Info
std::vector<std::tuple<std::string, std::string, int>> SMTCell::inst_partition;
std::map<int, int> SMTCell::h_inst_partition;
std::map<int, std::string> SMTCell::h_sdbInst;
std::vector<std::tuple<int, std::vector<int>, int>> SMTCell::inst_partition_p;
std::vector<std::tuple<int, std::vector<int>, int>> SMTCell::inst_partition_n;

// ### Power Net/Pin Info
std::map<unsigned int, int> SMTCell::h_pin_power;
std::map<unsigned int, int> SMTCell::h_net_power;

// ### Crostalk Mitigation Info
std::map<std::string, int> SMTCell::h_net_track;
std::map<int, std::vector<std::string>> SMTCell::h_track_net;

// ### Net Optimization
std::map<int, std::string> SMTCell::h_net_opt;

// ### Crossbar Info [Used in 3F_6T]
std::map<int, int> SMTCell::h_specialNet;

// ### Graph Variable
std::map<Triplet, std::shared_ptr<Vertex>> SMTCell::vertices;
std::vector<UdEdge *> SMTCell::udEdges;
std::vector<std::shared_ptr<Triplet>> SMTCell::boundaryVertices;
std::vector<OuterPin *> SMTCell::outerPins;
std::vector<std::shared_ptr<Triplet>> SMTCell::leftCorners;
std::vector<std::shared_ptr<Triplet>> SMTCell::rightCorners;
std::vector<std::shared_ptr<Triplet>> SMTCell::frontCorners;
std::vector<std::shared_ptr<Triplet>> SMTCell::backCorners;
std::map<std::string, std::shared_ptr<Source>> SMTCell::sources;
std::map<std::string, std::shared_ptr<Sink>> SMTCell::sinks;
std::vector<std::shared_ptr<VirtualEdge>> SMTCell::virtualEdges;
std::map<std::string, std::vector<int>> SMTCell::edge_in;
std::map<std::string, std::vector<int>> SMTCell::edge_out;
std::map<std::string, std::vector<int>> SMTCell::vedge_in;
std::map<std::string, std::vector<int>> SMTCell::vedge_out;

std::string SMTCell::keySON = "pinSON";

void SMTCell::debug_variable_assignment() {
  fmt::print("\n");
  fmt::print(
      "d     ##### DEBUG MODE: Checkpoint #{} Variable Assignment #####\n",
      SMTCell::get_debug_checkpoint());
  fmt::print("d     #     h_assign = {}\n", SMTCell::getAssignedCnt());
  fmt::print("d     #     h_assign_new = {}\n", SMTCell::getAssignedNewCnt());
  fmt::print("d     #     h_var = {}\n", SMTCell::getVarCnt());
  fmt::print(
      "d     #########################################################\n");
  fmt::print("\n");
}

void SMTCell::initTrackInfo(const std::string &config_path) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();

  // compatible with 4 track, 5 track, 6 track
  fmt::print("d     #     read track info\n");
  SMTCell::numTrack_ = config["NumTrack"]["value"];

  // MH configuration
  if (SMTCell::numTrack_ == 2 || SMTCell::numTrack_ == 4) {
    SMTCell::initMHInfo_helper_2T_4T(config_path);
  } else if (SMTCell::numTrack_ == 3) {
    SMTCell::initMHInfo_helper_3T(config_path);
  } else {
    std::cout << "[ERROR] Invalid number of tracks. SMTCell-MH supports 2T/3T/4T "
                 "options."
              << std::endl;
    exit(-1);
  }
  
  // AGR / Offset Information
  int m1_pitch = config["M1_Factor"]["value"];
  int m2_pitch = config["M2_Factor"]["value"];
  int m3_pitch = config["M3_Factor"]["value"];
  int m4_pitch = config["M4_Factor"]["value"];

  fmt::print("d     #     m1_pitch = {}\n", m1_pitch);
  fmt::print("d     #     m2_pitch = {}\n", m2_pitch);
  fmt::print("d     #     m3_pitch = {}\n", m3_pitch);
  fmt::print("d     #     m4_pitch = {}\n", m4_pitch);

  // temp solution for for having row in real distance
  int original_M3 = config["M1P"]["value"];
  int original_M2 = config["M0P"]["value"];
  SMTCell::row_distance = original_M2 * (m3_pitch / original_M3);
  fmt::print("d     #     uniform row distance = {}\n", SMTCell::row_distance);
  // if (SMTCell::DEBUG_MODE_) {
  //   fmt::print("d     #     row_disance = {}\n", SMTCell::row_distance);
  // }

  SMTCell::setMetalPitch(1, m1_pitch);
  SMTCell::setMetalPitch(2, m2_pitch);
  SMTCell::setMetalPitch(3, m3_pitch);
  SMTCell::setMetalPitch(4, m4_pitch);

  int m1_offset = config["M1_Offset"]["value"];
  int m2_offset = config["M2_Offset"]["value"];
  int m3_offset = config["M3_Offset"]["value"];
  int m4_offset = config["M4_Offset"]["value"];

  fmt::print("d     #     m1_offset = {}\n", m1_offset);
  fmt::print("d     #     m2_offset = {}\n", m2_offset);
  fmt::print("d     #     m3_offset = {}\n", m3_offset);
  fmt::print("d     #     m4_offset = {}\n", m4_offset);

  SMTCell::setOffset(1, m1_offset);
  SMTCell::setOffset(2, m2_offset);
  SMTCell::setOffset(3, m3_offset);
  SMTCell::setOffset(4, m4_offset);

  // # Placement vs. Routing Horizontal Track Mapping Array
  // # Placement vs. Routing Horizontal Track Mapping Array
  if (SMTCell::numTrack_ == 2) { // 1F3T FLAG
    // Tracks per Placement Row = 3
    SMTCell::mapTrack = {{0, 1}, {1, 1}, {2, 0}};
  } else if (SMTCell::numTrack_ == 3) { // 1F3T FLAG
    // Tracks per Placement Row = 3
    SMTCell::mapTrack = {{0, 2}, {1, 2}, {2, 0}, {3, 0}};
  } else if (SMTCell::numTrack_ == 4) {
    // Tracks per Placement Row = 3
    SMTCell::mapTrack = {{0, 3}, {1, 2}, {2, 1}, {3, 0}};
  } else if (SMTCell::numTrack_ == 5) {
    // Tracks per Placement Row = 3.5
    SMTCell::mapTrack = {{0, 4}, {1, 3}, {2, 3}, {3, 1}, {4, 1}, {5, 0}};
  } else if (SMTCell::numTrack_ == 6) {
    // Tracks per Placement Row = 4
    SMTCell::mapTrack = {{0, 5}, {1, 4}, {2, 4}, {3, 1}, {4, 1}, {5, 0}};
  } else {
    std::cout << "[ERROR] Invalid number of tracks. SMTCell supports 4T/5T/6T "
                 "options."
              << std::endl;
    exit(-1);
  }

  for (auto const &mt : SMTCell::mapTrack) {
    SMTCell::h_mapTrack[mt.second] = 1;
    SMTCell::h_RTrack[mt.first] = mt.second;
  }

  for (auto const &nc : SMTCell::numContact) {
    SMTCell::h_numConn[nc.first] = nc.second - 1;
  }
}

void SMTCell::initMHInfo_helper_2T_4T(const std::string &config_path) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();
  // set standard cell row count and order
  SMTCell::numTrackH_ = config["NumTrack"]["value"];
  SMTCell::placementRow_ = config["PlacementRow"]["value"];
  SMTCell::num_site = config["NumSite"]["value"];
  SMTCell::trackEachRow_ = config["TrackEachRow"]["value"];
  // ! why special case for 2 track?
  if (SMTCell::placementRow_ == 2) {
    // do nothing
    SMTCell::numTrackH_ =
      SMTCell::placementRow_ * SMTCell::num_site;
  } 
  // else if (SMTCell::placementRow_ == 3) {
  //   // do nothing
  //   SMTCell::numTrackH_ = SMTCell::placementRow_ * SMTCell::num_site;
  // } 
  else if (SMTCell::placementRow_ == 4) {
    SMTCell::placementRow_ /= SMTCell::num_site;
    SMTCell::numTrackH_ =
      SMTCell::placementRow_ * (SMTCell::trackEachRow_ - 1) * SMTCell::num_site;
  }
  fmt::print("debug-->     #     numTrackH_ = {}\n", SMTCell::numTrackH_);
  SMTCell::num_clip = config["NumClip"]["value"];
  SMTCell::order_clip = config["OrderClip"]["value"];
  std::string num_row_per_clip_str = config["NumRowPerClip"]["value"];
  int singleHeightRowCnt = SMTCell::numTrackH_ / SMTCell::num_site;
  fmt::print("debug-->     #     singleHeightRowCnt = {}\n",
             singleHeightRowCnt);
  // based on the num_row_per_clip_str, convert it to a map
  // "44" -> {4, 4}
  for (size_t i = 0; i < num_row_per_clip_str.size(); i++) {
    SMTCell::num_row_per_clip[i] = num_row_per_clip_str[i] - '0';
  }
  // generate the row mapping
  std::vector<std::vector<int>> tmp_pmos_placement_rows = {};
  std::vector<std::vector<int>> tmp_nmos_placement_rows = {};
  std::vector<int> tmp_pmos_placeable_rows = {};
  std::vector<int> tmp_nmos_placeable_rows = {};
  std::vector<std::vector<int>> tmp_pmos_routing_rows = {};
  std::vector<std::vector<int>> tmp_nmos_routing_rows = {};
  std::vector<int> tmp_pmos_pin_rows = {};
  std::vector<int> tmp_nmos_pin_rows = {};
  std::vector<int> tmp_pmos_gate_rows = {};
  std::vector<int> tmp_nmos_gate_rows = {};
  int row_idx = 0;
  std::vector<int> tmp_row = {};
  std::map<int, std::vector<int>> tmp_routing_rows = {};
  for (int i = 0; i < SMTCell::num_site; i++) {
    for (int j = 0; j < singleHeightRowCnt; j++) {
      tmp_row.push_back(row_idx);
      row_idx++;
    }
    tmp_routing_rows[i] = tmp_row;
    tmp_row.clear();
  }
  // generate the placement row mapping [reversed order]
  row_idx = SMTCell::numTrackH_ - 1;
  std::map<int, std::vector<int>> tmp_placement_rows = {};
  tmp_row.clear();
  for (int i = 0; i < SMTCell::num_site; i++) {
    for (int j = 0; j < singleHeightRowCnt; j++) {
      tmp_row.push_back(row_idx);
      row_idx--;
    }
    tmp_placement_rows[i] = tmp_row;
    tmp_row.clear();
  }
  // generate the routing mapping
  int clip_row_idx = 0;
  int clip_idx = 0;
  int row_idx_near_pwr_rail = 0;
  tmp_row.clear();
  // iter tmp_routing_rows
  for (auto const &i : tmp_routing_rows) {
    for (auto const &j : i.second) {
      tmp_row.push_back(j);
      // every clip row index, we need to switch to the next clip
      if (clip_row_idx == SMTCell::num_row_per_clip[clip_idx] - 1) {
        // if the clip_idx-th item inside rowOrder is 'P', then it is PMOS
        if (SMTCell::order_clip[clip_idx] == 'P') {
          // before push, sort the row in ascending order
          std::sort(tmp_row.begin(), tmp_row.end());
          // ! why use placement_rows instead of routing_rows?
          tmp_pmos_placement_rows.push_back(tmp_row);
          tmp_pmos_pin_rows.push_back(tmp_row[row_idx_near_pwr_rail]);
          if (row_idx_near_pwr_rail == 0) {
            row_idx_near_pwr_rail = tmp_row.size() - 1;
          } else {
            row_idx_near_pwr_rail = 0;
          }
        }
        // if the clip_idx-th item inside rowOrder is 'N', then it is NMOS
        if (SMTCell::order_clip[clip_idx] == 'N') {
          // before push, sort the row in ascending order
          std::sort(tmp_row.begin(), tmp_row.end());
          tmp_nmos_placement_rows.push_back(tmp_row);
          tmp_nmos_pin_rows.push_back(tmp_row[row_idx_near_pwr_rail]);
          if (row_idx_near_pwr_rail == 0) {
            row_idx_near_pwr_rail = tmp_row.size() - 1;
          } else {
            row_idx_near_pwr_rail = 0;
          }
        }
        // reset the row
        tmp_row.clear();
        clip_row_idx = 0;
        clip_idx++;
      } else {
        clip_row_idx++;
      }
    }
  }
  // print all the generated rows
  // reverse the order pmos_placement_rows : this will ensure the order is from
  // bottom to top
  std::reverse(tmp_pmos_placement_rows.begin(), tmp_pmos_placement_rows.end());
  // reverse the order nmos_placement_rows : this will ensure the order is from
  // bottom to top
  std::reverse(tmp_nmos_placement_rows.begin(), tmp_nmos_placement_rows.end());
  // generate the placement mapping
  clip_row_idx = 0;
  clip_idx = 0;
  row_idx_near_pwr_rail = 0;
  tmp_row.clear();
  // iter tmp_placement_rows
  for (auto const &i : tmp_placement_rows) {
    for (auto const &j : i.second) {
      tmp_row.push_back(j);
      // every clip row index, we need to switch to the next clip
      if (clip_row_idx == SMTCell::num_row_per_clip[clip_idx] - 1) {
        // if the clip_idx-th item inside rowOrder is 'P', then it is PMOS
        if (SMTCell::order_clip[clip_idx] == 'P') {
          // before push, sort the row in ascending order
          std::sort(tmp_row.begin(), tmp_row.end());
          // ! why use routing_rows instead of placement_rows?
          tmp_pmos_routing_rows.push_back(tmp_row);
        }
        // if the clip_idx-th item inside rowOrder is 'N', then it is NMOS
        if (SMTCell::order_clip[clip_idx] == 'N') {
          // before push, sort the row in ascending order
          std::sort(tmp_row.begin(), tmp_row.end());
          tmp_nmos_routing_rows.push_back(tmp_row);
        }
        // reset the row
        tmp_row.clear();
        clip_row_idx = 0;
        clip_idx++;
      } else {
        clip_row_idx++;
      }
    }
  }
  // // print tmp_routing_rows
  // to top
  std::reverse(tmp_pmos_routing_rows.begin(), tmp_pmos_routing_rows.end());
  // reverse the order nmos_routing : this will ensure the order is from bottom
  // to top
  std::reverse(tmp_nmos_routing_rows.begin(), tmp_nmos_routing_rows.end());
  // for placeable rows, take the first row of each clip
  for (size_t i = 0; i < tmp_pmos_placement_rows.size(); i++) {
    tmp_pmos_placeable_rows.push_back(tmp_pmos_placement_rows[i][0]);
  }
  for (size_t i = 0; i < tmp_nmos_placement_rows.size(); i++) {
    tmp_nmos_placeable_rows.push_back(tmp_nmos_placement_rows[i][0]);
  }
  // // print tmp_pmos_placeable_rows
  // fmt::print("d     #     tmp_pmos_placeable_rows\n");
  // for (size_t i = 0; i < tmp_pmos_placeable_rows.size(); i++) {
  //   fmt::print("d     #     {}\n", tmp_pmos_placeable_rows[i]);
  // }
  // // print tmp_nmos_placeable_rows
  // fmt::print("d     #     tmp_nmos_placeable_rows\n");
  // for (size_t i = 0; i < tmp_nmos_placeable_rows.size(); i++) {
  //   fmt::print("d     #     {}\n", tmp_nmos_placeable_rows[i]);
  // }

  // for gate rows, take the rows that are cloest to power rails
  if (SMTCell::order_clip == "NPPN") {
    // for PMOS: take first row in the first clip and last row in the second
    // clip
    tmp_pmos_gate_rows.push_back(tmp_pmos_placement_rows[0][0]); // ! bug
    tmp_pmos_gate_rows.push_back(
        tmp_pmos_placement_rows[1][tmp_pmos_placement_rows[1].size() - 1]);
    // for NMOS: take last row in the first clip and first row in the second
    // clip
    tmp_nmos_gate_rows.push_back(
        tmp_nmos_placement_rows[0][tmp_nmos_placement_rows[0].size() - 1]);
    tmp_nmos_gate_rows.push_back(tmp_nmos_placement_rows[1][0]);
  } else if (SMTCell::order_clip == "PNNP") {
    // for PMOS: take last row in the first clip and first row in the second
    // clip
    tmp_pmos_gate_rows.push_back(
        tmp_pmos_placement_rows[0][tmp_pmos_placement_rows[0].size() - 1]);
    tmp_pmos_gate_rows.push_back(tmp_pmos_placement_rows[1][0]);
    // for NMOS: take first row in the first clip and last row in the second
    // clip
    tmp_nmos_gate_rows.push_back(tmp_nmos_placement_rows[0][0]);
    tmp_nmos_gate_rows.push_back(
        tmp_nmos_placement_rows[1][tmp_nmos_placement_rows[1].size() - 1]);
  } else {
    fmt::print("d     #     Invalid order_clip\n");
    exit(-1);
  }

  // print all the generated rows
  fmt::print("d     #     tmp_routing_rows\n");
  for (auto const &i : tmp_routing_rows) {
    fmt::print("d     #     ");
    for (auto const &j : i.second) {
      fmt::print("{} ", j);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     tmp_placement_rows\n");
  for (auto const &i : tmp_placement_rows) {
    fmt::print("d     #     ");
    for (auto const &j : i.second) {
      fmt::print("{} ", j);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     pmos_placement_rows\n");
  for (size_t i = 0; i < tmp_pmos_placement_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_pmos_placement_rows[i].size(); j++) {
      fmt::print("{} ", tmp_pmos_placement_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     nmos_placement_rows\n");
  for (size_t i = 0; i < tmp_nmos_placement_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_nmos_placement_rows[i].size(); j++) {
      fmt::print("{} ", tmp_nmos_placement_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     pmos_routing_rows\n");
  for (size_t i = 0; i < tmp_pmos_routing_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_pmos_routing_rows[i].size(); j++) {
      fmt::print("{} ", tmp_pmos_routing_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     nmos_routing_rows\n");
  for (size_t i = 0; i < tmp_nmos_routing_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_nmos_routing_rows[i].size(); j++) {
      fmt::print("{} ", tmp_nmos_routing_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     pmos_placeable_rows\n");
  for (size_t i = 0; i < tmp_pmos_placeable_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_pmos_placeable_rows[i]);
  }
  fmt::print("d     #     nmos_placeable_rows\n");
  for (size_t i = 0; i < tmp_nmos_placeable_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_nmos_placeable_rows[i]);
  }
  fmt::print("d     #     pmos_pin_rows\n");
  for (size_t i = 0; i < tmp_pmos_pin_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_pmos_pin_rows[i]);
  }
  fmt::print("d     #     nmos_pin_rows\n");
  for (size_t i = 0; i < tmp_nmos_pin_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_nmos_pin_rows[i]);
  }
  fmt::print("d     #     pmos_gate_rows\n");
  for (size_t i = 0; i < tmp_pmos_gate_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_pmos_gate_rows[i]);
  }
  fmt::print("d     #     nmos_gate_rows\n");
  for (size_t i = 0; i < tmp_nmos_gate_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_nmos_gate_rows[i]);
  }
  // set the global variables
  SMTCell::mh_placement_rows = tmp_placement_rows;
  SMTCell::mh_routing_rows = tmp_routing_rows;
  SMTCell::mh_pmos_placement_rows = tmp_pmos_placement_rows;
  SMTCell::mh_nmos_placement_rows = tmp_nmos_placement_rows;
  SMTCell::mh_pmos_placeable_rows = tmp_pmos_placeable_rows;
  SMTCell::mh_nmos_placeable_rows = tmp_nmos_placeable_rows;
  SMTCell::mh_pmos_routing_rows = tmp_pmos_routing_rows;
  SMTCell::mh_nmos_routing_rows = tmp_nmos_routing_rows;
  SMTCell::mh_pmos_pin_rows = tmp_pmos_pin_rows;
  SMTCell::mh_nmos_pin_rows = tmp_nmos_pin_rows;
  SMTCell::mh_pmos_gate_rows = tmp_pmos_gate_rows;
  SMTCell::mh_nmos_gate_rows = tmp_nmos_gate_rows;
  // free the memory
  tmp_placement_rows.clear();
  tmp_routing_rows.clear();
  tmp_pmos_placement_rows.clear();
  tmp_nmos_placement_rows.clear();
  tmp_pmos_routing_rows.clear();
  tmp_nmos_routing_rows.clear();
  tmp_pmos_pin_rows.clear();
  tmp_nmos_pin_rows.clear();
  tmp_pmos_placeable_rows.clear();
  tmp_nmos_placeable_rows.clear();
  tmp_pmos_gate_rows.clear();
  tmp_nmos_gate_rows.clear();
}

void SMTCell::initMHInfo_helper_3T(const std::string &config_path) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();
  // set standard cell row count and order
  SMTCell::numTrackH_ = config["NumTrack"]["value"];
  SMTCell::placementRow_ = config["PlacementRow"]["value"];
  SMTCell::num_site = config["NumSite"]["value"];
  SMTCell::trackEachRow_ = config["TrackEachRow"]["value"];
  // ! why special case for 2 track?
  if (SMTCell::placementRow_ == 3) {
    SMTCell::numTrackH_ = SMTCell::placementRow_ * SMTCell::num_site;
  } 
  fmt::print("debug-->     #     numTrackH_ = {}\n", SMTCell::numTrackH_);
  SMTCell::num_clip = config["NumClip"]["value"];
  SMTCell::order_clip = config["OrderClip"]["value"];
  std::string num_row_per_clip_str = config["NumRowPerClip"]["value"];
  int singleHeightRowCnt = SMTCell::numTrackH_ / SMTCell::num_site;
  fmt::print("debug-->     #     singleHeightRowCnt = {}\n",
             singleHeightRowCnt);
  // based on the num_row_per_clip_str, convert it to a map
  // "44" -> {4, 4}
  for (size_t i = 0; i < num_row_per_clip_str.size(); i++) {
    SMTCell::num_row_per_clip[i] = num_row_per_clip_str[i] - '0';
  }
  // generate the row mapping
  std::vector<std::vector<int>> tmp_pmos_placement_rows = {};
  std::vector<std::vector<int>> tmp_nmos_placement_rows = {};
  std::vector<int> tmp_pmos_placeable_rows = {};
  std::vector<int> tmp_nmos_placeable_rows = {};
  std::vector<std::vector<int>> tmp_pmos_routing_rows = {};
  std::vector<std::vector<int>> tmp_nmos_routing_rows = {};
  std::vector<int> tmp_pmos_pin_rows = {};
  std::vector<int> tmp_nmos_pin_rows = {};
  std::vector<int> tmp_pmos_gate_rows = {};
  std::vector<int> tmp_nmos_gate_rows = {};
  int row_idx = 0;
  std::vector<int> tmp_row = {};
  std::map<int, std::vector<int>> tmp_routing_rows = {};
  for (int i = 0; i < SMTCell::num_site; i++) {
    for (int j = 0; j < singleHeightRowCnt; j++) {
      tmp_row.push_back(row_idx);
      row_idx++;
    }
    tmp_routing_rows[i] = tmp_row;
    tmp_row.clear();
  }
  // generate the placement row mapping [reversed order]
  row_idx = SMTCell::numTrackH_ - 1;
  std::map<int, std::vector<int>> tmp_placement_rows = {};
  tmp_row.clear();
  for (int i = 0; i < SMTCell::num_site; i++) {
    for (int j = 0; j < singleHeightRowCnt; j++) {
      tmp_row.push_back(row_idx);
      row_idx--;
    }
    tmp_placement_rows[i] = tmp_row;
    tmp_row.clear();
  }
  // TODO: assign tmp_pmos_placement_rows, tmp_pmos_pin_rows, tmp_nmos_placement_rows, tmp_nmos_pin_rows
  if (SMTCell::order_clip == "NPPN") {
    tmp_pmos_placement_rows = {{3}, {2}};
    tmp_nmos_placement_rows = {{5}, {0}};
    tmp_pmos_pin_rows = {2, 3};
    tmp_nmos_pin_rows = {0, 5};
    tmp_pmos_routing_rows = {{2}, {3}};
    tmp_nmos_routing_rows = {{0}, {5}};
    tmp_pmos_placeable_rows = {{3}, {2}};
    tmp_nmos_placeable_rows = {{5}, {0}};
    tmp_pmos_gate_rows = {{3}, {2}};
    tmp_nmos_gate_rows = {{5}, {0}};
  } else if (SMTCell::order_clip == "PNNP") {
    tmp_pmos_placement_rows = {{5}, {0}};
    tmp_nmos_placement_rows = {{3}, {2}};
    tmp_pmos_pin_rows = {0, 5};
    tmp_nmos_pin_rows = {2, 3};
    tmp_pmos_routing_rows = {{0}, {5}};
    tmp_nmos_routing_rows = {{2}, {3}};
    tmp_pmos_placeable_rows = {{5}, {0}};
    tmp_nmos_placeable_rows = {{3}, {2}};
    tmp_pmos_gate_rows = {{0}, {5}};
    tmp_nmos_gate_rows = {{2}, {3}};
  } else {
    fmt::print("d     #     Invalid order_clip\n");
    exit(-1);
  }

  // print all the generated rows
  fmt::print("d     #     tmp_routing_rows\n");
  for (auto const &i : tmp_routing_rows) {
    fmt::print("d     #     ");
    for (auto const &j : i.second) {
      fmt::print("{} ", j);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     tmp_placement_rows\n");
  for (auto const &i : tmp_placement_rows) {
    fmt::print("d     #     ");
    for (auto const &j : i.second) {
      fmt::print("{} ", j);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     pmos_placement_rows\n");
  for (size_t i = 0; i < tmp_pmos_placement_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_pmos_placement_rows[i].size(); j++) {
      fmt::print("{} ", tmp_pmos_placement_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     nmos_placement_rows\n");
  for (size_t i = 0; i < tmp_nmos_placement_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_nmos_placement_rows[i].size(); j++) {
      fmt::print("{} ", tmp_nmos_placement_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     pmos_routing_rows\n");
  for (size_t i = 0; i < tmp_pmos_routing_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_pmos_routing_rows[i].size(); j++) {
      fmt::print("{} ", tmp_pmos_routing_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     nmos_routing_rows\n");
  for (size_t i = 0; i < tmp_nmos_routing_rows.size(); i++) {
    fmt::print("d     #     ");
    for (size_t j = 0; j < tmp_nmos_routing_rows[i].size(); j++) {
      fmt::print("{} ", tmp_nmos_routing_rows[i][j]);
    }
    fmt::print("\n");
  }
  fmt::print("d     #     pmos_placeable_rows\n");
  for (size_t i = 0; i < tmp_pmos_placeable_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_pmos_placeable_rows[i]);
  }
  fmt::print("d     #     nmos_placeable_rows\n");
  for (size_t i = 0; i < tmp_nmos_placeable_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_nmos_placeable_rows[i]);
  }
  fmt::print("d     #     pmos_pin_rows\n");
  for (size_t i = 0; i < tmp_pmos_pin_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_pmos_pin_rows[i]);
  }
  fmt::print("d     #     nmos_pin_rows\n");
  for (size_t i = 0; i < tmp_nmos_pin_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_nmos_pin_rows[i]);
  }
  fmt::print("d     #     pmos_gate_rows\n");
  for (size_t i = 0; i < tmp_pmos_gate_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_pmos_gate_rows[i]);
  }
  fmt::print("d     #     nmos_gate_rows\n");
  for (size_t i = 0; i < tmp_nmos_gate_rows.size(); i++) {
    fmt::print("d     #     {}\n", tmp_nmos_gate_rows[i]);
  }
  // set the global variables
  SMTCell::mh_placement_rows = tmp_placement_rows;
  SMTCell::mh_routing_rows = tmp_routing_rows;
  SMTCell::mh_pmos_placement_rows = tmp_pmos_placement_rows;
  SMTCell::mh_nmos_placement_rows = tmp_nmos_placement_rows;
  SMTCell::mh_pmos_placeable_rows = tmp_pmos_placeable_rows;
  SMTCell::mh_nmos_placeable_rows = tmp_nmos_placeable_rows;
  SMTCell::mh_pmos_routing_rows = tmp_pmos_routing_rows;
  SMTCell::mh_nmos_routing_rows = tmp_nmos_routing_rows;
  SMTCell::mh_pmos_pin_rows = tmp_pmos_pin_rows;
  SMTCell::mh_nmos_pin_rows = tmp_nmos_pin_rows;
  SMTCell::mh_pmos_gate_rows = tmp_pmos_gate_rows;
  SMTCell::mh_nmos_gate_rows = tmp_nmos_gate_rows;
  // free the memory
  tmp_placement_rows.clear();
  tmp_routing_rows.clear();
  tmp_pmos_placement_rows.clear();
  tmp_nmos_placement_rows.clear();
  tmp_pmos_routing_rows.clear();
  tmp_nmos_routing_rows.clear();
  tmp_pmos_pin_rows.clear();
  tmp_nmos_pin_rows.clear();
  tmp_pmos_placeable_rows.clear();
  tmp_nmos_placeable_rows.clear();
  tmp_pmos_gate_rows.clear();
  tmp_nmos_gate_rows.clear();
}

void SMTCell::setPlacementRow(int placementRow) {
  SMTCell::placementRow_ = placementRow;
}

void SMTCell::setTrackEachRow(float trackEachRow) {
  SMTCell::trackEachRow_ = trackEachRow;
}

void SMTCell::setTrackEachPRow(int trackEachPRow) {
  SMTCell::trackEachPRow_ = trackEachPRow;
}

void SMTCell::setNumTrackH(int numTrackH) { SMTCell::numTrackH_ = numTrackH; }

void SMTCell::setNumTrackV(int numTrackV) { SMTCell::numTrackV_ = numTrackV; }

void SMTCell::setNumMetalLayer(int numMetalLayer) {
  SMTCell::numMetalLayer_ = numMetalLayer;
}

void SMTCell::setNumPTrackH(int numPTrackH) {
  SMTCell::numPTrackH_ = numPTrackH;
}

void SMTCell::setNumPTrackV(int numPTrackV) {
  SMTCell::numPTrackV_ = numPTrackV;
}

// AGR FLAG : Changed to real distance
// by default add (4+1)
int SMTCell::getBitLength_numTrackV() {
  if (SMTCell::standardCellWidth > 0) {
    // return bmp::msb(SMTCell::standardCellWidth) + 5;
    return bmp::msb(SMTCell::getNumTrackV()) + 5;
  } else {
    // use fmt to print to stderr
    fmt::print(stderr, "[ERROR] Calling Bit Length before standardCellWidth "
                       "is set\n");
    exit(1);
  }
}

// by default add (+1)
int SMTCell::getBitLength_numTrackH() {
  if (SMTCell::numTrackH_ > 0) {
    return bmp::msb(SMTCell::numTrackH_) + 1;
  } else {
    // use fmt to print to stderr
    fmt::print(stderr, "[ERROR] Calling Bit Length before numTrackH is set\n");
    exit(1);
  }
}

// by default add (+1)
int SMTCell::getBitLength_numPTrackH() {
  if (SMTCell::numPTrackH_ > 0) {
    return bmp::msb(SMTCell::numPTrackH_) + 1;
  } else {
    std::cerr << "[ERROR] Calling Bit Length before numPTrackH is set\n";
    exit(1);
  }
}

// by default add (+1)
int SMTCell::getBitLength_trackEachPRow() {
  if (SMTCell::trackEachPRow_ > 0) {
    return bmp::msb(SMTCell::trackEachPRow_) + 1;
  } else {
    std::cerr << "[ERROR] Calling Bit Length before trackEachPRow is set\n";
    exit(1);
  }
}

void SMTCell::cnt(std::string type, int idx) {
  // Variable
  if (type == "v") {
    switch (idx) {
    case 0:
      SMTCell::c_v_placement_++;
      break;
    case 1:
      SMTCell::c_v_placement_aux_++;
      break;
    case 2:
      SMTCell::c_v_routing_++;
      break;
    case 3:
      SMTCell::c_v_routing_aux_++;
      break;
    case 4:
      SMTCell::c_v_connect_++;
      break;
    case 5:
      SMTCell::c_v_connect_aux_++;
      break;
    case 6:
      SMTCell::c_v_dr_++;
      break;
    default:
      std::cout << "a     [WARNING] Count Option is Invalid!! [type=" << type
                << ", idx=" << idx << "]\n";
      exit(1);
    }
  } else if (type == "c") { // Constraints
    switch (idx) {
    case 0:
      SMTCell::c_c_placement_++;
      break;
    case 1:
      SMTCell::c_c_routing_++;
      break;
    case 2:
      SMTCell::c_c_connect_++;
      break;
    case 3:
      SMTCell::c_c_dr_++;
      break;
    case 4:
      std::cout << "a     [WARNING] Count Option is Invalid!! [type=" << type
                << ", idx=" << idx << "]\n";
      exit(1);
    }
  } else if (type == "l") { // Literals
    switch (idx) {
    case 0:
      SMTCell::c_l_placement_++;
      break;
    case 1:
      SMTCell::c_l_routing_++;
      break;
    case 2:
      SMTCell::c_l_connect_++;
      break;
    case 3:
      SMTCell::c_l_dr_++;
      break;
    default:
      std::cout << "a     [WARNING] Count Option is Invalid!! [type=" << type
                << ", idx=" << idx << "]\n";
      exit(1);
    }
  } else {
    std::cout << "a     [WARNING] Count Option is Invalid!! [type=" << type
              << ", idx=" << idx << "]\n";
    exit(1);
  }
}

std::vector<std::vector<int>> SMTCell::combine(std::vector<int> &l,
                                               std::size_t n) {
  if (n > l.size()) {
    throw "Insufficient l members";
  }

  if (n <= 1) {
    std::vector<std::vector<int>> result;
    for (int x : l) {
      std::vector<int> temp;
      temp.push_back(x);
      result.push_back(temp);
    }
    return result;
  }

  std::vector<std::vector<int>> comb;
  int val = l[0];
  std::vector<int> rest(l.begin() + 1, l.end());
  auto sub_comb = SMTCell::combine_sub(rest, n - 1);
  for (auto &v : sub_comb) {
    v.insert(v.begin(), val);
    comb.push_back(v);
  }

  return comb;
}

std::vector<std::vector<int>> SMTCell::combine_sub(std::vector<int> &l,
                                                   std::size_t n) {
  if (n > l.size()) {
    throw "Insufficient l members";
    exit(1);
  }

  if (n <= 1) {
    std::vector<std::vector<int>> result;
    for (int x : l) {
      std::vector<int> temp;
      temp.push_back(x);
      result.push_back(temp);
    }
    return result;
  }

  std::vector<std::vector<int>> comb;
  for (std::size_t i = 0; i + n <= l.size(); ++i) {
    int val = l[i];
    std::vector<int> rest(l.begin() + i + 1, l.end());
    auto sub_comb = SMTCell::combine_sub(rest, n - 1);
    for (auto &v : sub_comb) {
      v.insert(v.begin(), val);
      comb.push_back(v);
    }
  }
  return comb;
}

void SMTCell::reset_cnt() {
  SMTCell::c_v_placement_ = 0;
  SMTCell::c_v_placement_aux_ = 0;
  SMTCell::c_v_routing_ = 0;
  SMTCell::c_v_routing_aux_ = 0;
  SMTCell::c_v_connect_ = 0;
  SMTCell::c_v_connect_aux_ = 0;
  SMTCell::c_v_dr_ = 0;
  SMTCell::c_c_placement_ = 0;
  SMTCell::c_c_routing_ = 0;
  SMTCell::c_c_connect_ = 0;
  SMTCell::c_c_dr_ = 0;
  SMTCell::c_l_placement_ = 0;
  SMTCell::c_l_routing_ = 0;
  SMTCell::c_l_connect_ = 0;
  SMTCell::c_l_dr_ = 0;
}

void SMTCell::reset_var() {
  SMTCell::clear_writeout();
  SMTCell::h_var.clear();
  SMTCell::idx_var_ = 1;
}

void SMTCell::clear_writeout() { SMTCell::writeout = ""; }

void SMTCell::writeConstraint(std::string str) { SMTCell::writeout += str; }

std::string SMTCell::readConstraint() { return SMTCell::writeout; }

bool SMTCell::setVar(std::string varName, int type) {
  // not exist
  if (SMTCell::h_var.find(varName) == SMTCell::h_var.end()) {
    // why this is type not index?
    cnt("v", type);
    SMTCell::h_var[varName] = SMTCell::idx_var_;
    SMTCell::idx_var_++;
    return true;
  }
  return false;
}

bool SMTCell::setVar_wo_cnt(std::string varName, int type) {
  // not exist
  if (SMTCell::h_var.find(varName) == SMTCell::h_var.end()) {
    SMTCell::h_var[varName] = -1;
    return true;
  }
  return false;
}

int SMTCell::getTotalVar() {
  return SMTCell::c_v_placement_ + SMTCell::c_v_placement_aux_ +
         SMTCell::c_v_routing_ + SMTCell::c_v_routing_aux_ +
         SMTCell::c_v_connect_ + SMTCell::c_v_connect_aux_ + SMTCell::c_v_dr_;
}

int SMTCell::getTotalClause() {
  return SMTCell::c_c_placement_ + SMTCell::c_c_routing_ +
         SMTCell::c_c_connect_ + SMTCell::c_c_dr_;
}

int SMTCell::getTotalLiteral() {
  return SMTCell::c_l_placement_ + SMTCell::c_l_routing_ +
         SMTCell::c_l_connect_ + SMTCell::c_l_dr_;
}

void SMTCell::dump_summary() {
  std::cout << "a     ########## Summary ##########\n";
  std::cout << "a     # var for placement       = " << SMTCell::c_v_placement_
            << "\n";
  std::cout << "a     # var for placement(aux)  = "
            << SMTCell::c_v_placement_aux_ << "\n";
  std::cout << "a     # var for routing         = " << SMTCell::c_v_routing_
            << "\n";
  std::cout << "a     # var for routing(aux)    = " << SMTCell::c_v_routing_aux_
            << "\n";
  std::cout << "a     # var for design rule     = " << SMTCell::c_v_dr_ << "\n";
  std::cout << "a     # literals for placement   = " << SMTCell::c_l_placement_
            << "\n";
  std::cout << "a     # literals for routing     = " << SMTCell::c_l_routing_
            << "\n";
  std::cout << "a     # literals for design rule = " << SMTCell::c_l_dr_
            << "\n";
  std::cout << "a     # clauses for placement   = " << SMTCell::c_c_placement_
            << "\n";
  std::cout << "a     # clauses for routing     = " << SMTCell::c_c_routing_
            << "\n";
  std::cout << "a     # clauses for design rule = " << SMTCell::c_c_dr_ << "\n";
}

std::vector<int> SMTCell::getAvailableNumFinger(int w,
                                                int track_each_placement_row) {
  std::vector<int> numFinger;
  for (int i = 0; i < track_each_placement_row; i++) {
    if (w % (track_each_placement_row - i) == 0) {
      numFinger.push_back(w / (track_each_placement_row - i));
      break;
    }
  }
  return numFinger;
}