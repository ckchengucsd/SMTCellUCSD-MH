#define FMT_HEADER_ONLY
#include "convSMTResult.hpp"
#include <algorithm>
#include <boost/algorithm/string/split.hpp>          // Include for boost::split
#include <boost/multiprecision/integer.hpp>          // for returning bit length
#include <boost/regex.hpp>
#include <cmath>
#include <filesystem>
#include <fmt/core.h>
#include <fmt/format.h>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <regex>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// input/output files
std::string infile;
std::string workdir;
std::string pinLayoutPath;
std::string cellName;

int M1_FACTOR = 60;
int M3_FACTOR = 80;

std::filesystem::path outdir;
std::filesystem::path outfile;

// print unnessary net info or not
bool DEBUG_MOD = false;

// ### Pre-processing ########################################################
int main(int argc, char **argv) {
  char temp[200];
  getcwd(temp, 200);
  workdir = temp;
  outdir /= workdir;

  if (argc != 7) {
    fmt::print("\n*** Error:: Wrong CMD");
    fmt::print("\n   [USAGE]: ./PL_FILE [inputfile_result] [org_cell_name] "
               "[output_dir] [pinLayout_dir] [M1_FACTOR] [M3_FACTOR]\n\n");
    exit(-1);
  } else {
    infile = argv[1];
    cellName = argv[2];
    outdir /= argv[3];
    pinLayoutPath = argv[4];
    M1_FACTOR = std::stoi(argv[5]);
    M3_FACTOR = std::stoi(argv[6]);
  }

  if (!std::filesystem::exists(infile)) {
    fmt::print("\n*** Error:: Input file does not exist");
    fmt::print("\n   [USAGE]: ./PL_FILE [inputfile_result] [org_cell_name] "
               "[output_dir] [pinLayout_dir] [M1_FACTOR] [M3_FACTOR]\n\n");
    exit(-1);
  }

  if (!std::filesystem::exists(pinLayoutPath)) {
    fmt::print("\n*** Error:: PinLayout file does not exist");
    fmt::print("\n   [USAGE]: ./PL_FILE [inputfile_result] [org_cell_name] "
               "[output_dir] [pinLayout_dir] [M1_FACTOR] [M3_FACTOR]\n\n");
    exit(-1);
  }

  // ### Output Directory Creation
  std::string command = "mkdir -p " + outdir.generic_string();

  std::string infileStatus = "init";

  // ## Instance Info
  // std::vector<InstVar *> insts;
  std::vector<std::shared_ptr<InstVar>> insts;
  std::map<unsigned int, int> h_inst_idx;
  int idx_inst = 0;

  // ## Metal/VIA Info

  // use shared_ptr to avoid memory leak
  std::vector<std::shared_ptr<MetalVar>> metals;
  std::vector<std::shared_ptr<ViaVar>> vias;
  std::vector<std::shared_ptr<MetalVar>> final_metal;
  std::vector<std::shared_ptr<ViaVar>> final_via;
  std::vector<std::shared_ptr<MetalVar>> m_metal;
  std::map<unsigned int, int> h_metal;

  // sort by row and col then merge into metals
  std::map<int, std::vector<int>> M1_metal_V;
  std::map<int, std::vector<int>> M2_metal_H;
  std::map<int, std::vector<int>> M3_metal_V;
  std::map<int, std::vector<int>> M4_metal_H;

  std::map<unsigned int, int> h_m_metal;
  // int idx_m_metal = 0;

  // ## Wire Info
  // std::vector<WireVar *> wires;
  // std::vector<ViaWireVar *> via_wires;
  std::vector<std::shared_ptr<WireVar>> wires;
  std::vector<std::shared_ptr<ViaWireVar>> via_wires;
  std::map<std::string, int> h_all_wire; // temp solution
  std::map<unsigned int, int> h_via_wire;

  // ## Instance Pin Info
  // std::vector<PinVar *> pins;
  // std::vector<ExtPinVar *> extpins;
  std::vector<std::shared_ptr<PinVar>> pins;
  std::vector<std::shared_ptr<ExtPinVar>> extpins;
  std::map<unsigned int, int> h_pin;
  std::map<unsigned int, int> h_extpin;

  // ## Net Info
  // std::vector<NetVar *> nets;
  std::vector<std::shared_ptr<NetVar>> nets;
  std::map<std::string, int> h_net;   // temp solution

  // ## LISD Info
  std::map<int, std::vector<int>> lisd_cols;

  // ## Gate Cut Info
  std::map<int, std::vector<int>> gc_cols;

  // ## Pass Through Info
  std::vector<int> pass_throughs;

  // ## Cost Info
  int cost_placement = 0;
  int cost_ml = 0;
  int cost_ml2 = 0;
  int cost_wl = 0;
  int no_m2_tracks = 0;

  // int isFirst = 1;
  // int subIndex = 0;

  // std::string out;
  std::string outfile;

  // ### Read External Pin Name
  std::map<int, std::string> h_extpin_name;
  std::map<int, std::string> h_extpin_type;

  int numTrackV = 0;
  int numTrackH = 0;
  float numTrackHPerClip = 0;
  int numRoutingClip = 0;

  // Read Inputfile and Build Data Structure
  std::string line;
  std::ifstream pinLayoutfileStream(pinLayoutPath);
  while (getline(pinLayoutfileStream, line)) {
    boost::smatch m;
    // Write this regex from perl: /^i.*pin.*net(\d+) ext (\S+) t -1 (\S+)/
    if (boost::regex_search(
            line, m,
            boost::regex("^i.*pin.*net(\\d+) ext (\\S+) t -1 (\\S+)"))) {
      int netID = std::stoi(m[1]);
      std::string pinName = m[2];
      std::string pinType = m[3];
      h_extpin_name[netID] = pinName;
      h_extpin_type[netID] = pinType;
    }

    // Translate this regex from perl: /^a.*Height of Routing Clip.*= (\S+)/
    if (boost::regex_search(
            line, m, boost::regex("^a.*Height of Routing Clip.*= (\\S+)"))) {
      numRoutingClip = std::stoi(m[1]);
      fmt::print("a     numRoutingClip: {}\n", numRoutingClip);
    }

    // Translate this regex from perl: /^a.*Width of Routing Clip.*= (\S+)/
    if (boost::regex_search(
            line, m, boost::regex("^a.*Width of Routing Clip.*= (\\S+)"))) {
      numTrackV = std::stoi(m[1]);
      // fmt::print("numTrackV: {}\n", numTrackV);
    }

    // Translate this regex from perl: /^a.*Tracks per Placement Row.*= (\S+)/
    if (boost::regex_search(
            line, m, boost::regex("^a.*Tracks per Placement Row.*= (\\d+(.?)\\d*)"))) {
      // This can be a float number
      numTrackHPerClip = std::stof(m[1]);
      fmt::print("a     numTrackHPerClip: {}\n", numTrackHPerClip);
    }
  }

  // pinLayoutfileStream.close();

  numTrackH = numRoutingClip * numTrackHPerClip - 2;

  // ### Read Inputfile and Build Data Structure
  std::ifstream infileStream(infile);
  while (getline(infileStream, line)) {
    boost::smatch m;

    // ### Instance Info ###
    // Translate this regex to C++ from perl: /^.*\(define-fun x(\d+)/
    if (boost::regex_search(line, m,
                            boost::regex("^.*\\(define-fun x(\\d+)"))) {
      int tmp = std::stoi(m[1]);
      // read next line
      getline(infileStream, line);

      int x;
      // translate this regex to C++ from perl: /^\s+#x(\S+)\)/
      if (boost::regex_search(line, m, boost::regex("^    #x(\\S+)\\)"))) {
        std::string x_hex =
            "0x" +
            boost::regex_replace(line, boost::regex("^\\s+#x(\\S+)\\)"), "$1");
        x = std::stoul(x_hex, nullptr, 16);
      } else if (boost::regex_search(line, m,
                                     boost::regex("^    #b(\\S+)\\)"))) {
        std::string x_binary =
            boost::regex_replace(line, boost::regex("^\\s+#b(\\S+)\\)"), "$1");
        x = std::stoi(x_binary, nullptr, 2);
      }
      x = x * M1_FACTOR;
      if (h_inst_idx.find(tmp) != h_inst_idx.end()) {
        insts[h_inst_idx.at(tmp)]->setxPos(x);
      } else {
        // InstVar *tmp_inst_var = new InstVar(tmp, x, -1, -1, -1, -1, -1);
        std::shared_ptr<InstVar> tmp_inst_var =
            std::make_shared<InstVar>(tmp, x, -1, -1, -1, -1, -1);
        insts.push_back(tmp_inst_var);
        h_inst_idx[tmp] = idx_inst;
        idx_inst++;
      }
    } else if (boost::regex_search(line, m,
                                   boost::regex("^.*\\(define-fun y(\\d+)"))) {
      int tmp = std::stoi(m[1]);
      // read next line
      getline(infileStream, line);

      int y;
      // translate this regex to C++ from perl: /^\s+#x(\S+)\)/
      if (boost::regex_search(line, m, boost::regex("^    #y(\\S+)\\)"))) {
        std::string y_hex =
            "0x" +
            boost::regex_replace(line, boost::regex("^\\s+#x(\\S+)\\)"), "$1");
        y = std::stoul(y_hex, nullptr, 16);
      } else if (boost::regex_search(line, m,
                                     boost::regex("^    #b(\\S+)\\)"))) {
        std::string y_binary =
            boost::regex_replace(line, boost::regex("^\\s+#b(\\S+)\\)"), "$1");
        y = std::stoi(y_binary, nullptr, 2);
      }

      if (h_inst_idx.find(tmp) != h_inst_idx.end()) {
        insts[h_inst_idx.at(tmp)]->setyPos(y);
      } else {
        // InstVar *tmp_inst_var = new InstVar(tmp, -1, y, -1, -1, -1, -1);
        std::shared_ptr<InstVar> tmp_inst_var =
            std::make_shared<InstVar>(tmp, -1, y, -1, -1, -1, -1);
        insts.push_back(tmp_inst_var);
        h_inst_idx[tmp] = idx_inst;
        idx_inst++;
      }
    } else if (boost::regex_search(line, m,
                                   boost::regex("^.*\\(define-fun nf(\\d+)"))) {
      int tmp = std::stoi(m[1]);
      // read next line
      getline(infileStream, line);

      int nf;
      if (boost::regex_search(line, m, boost::regex("^    #x(\\S+)\\)"))) {
        std::string nf_hex =
            "0x" +
            boost::regex_replace(line, boost::regex("^\\s+#x(\\S+)\\)"), "$1");
        nf = std::stoul(nf_hex, nullptr, 16);
      } else if (boost::regex_search(line, m, boost::regex("^    #b(\\S+)\\)"))) {
        std::string nf_binary =
            boost::regex_replace(line, boost::regex("^\\s+#b(\\S+)\\)"), "$1");
        nf = std::stoi(nf_binary, nullptr, 2);
      }

      if (h_inst_idx.find(tmp) != h_inst_idx.end()) {
        insts[h_inst_idx.at(tmp)]->setNumFinger(nf);
      } else {
        // InstVar *tmp_inst_var = new InstVar(tmp, -1, -1, nf, -1, -1, -1);
        std::shared_ptr<InstVar> tmp_inst_var =
            std::make_shared<InstVar>(tmp, -1, -1, nf, -1, -1, -1);
        insts.push_back(tmp_inst_var);
        h_inst_idx[tmp] = idx_inst;
        idx_inst++;
      }
    } else if (boost::regex_search(line, m,
                                   boost::regex("^.*\\(define-fun ff(\\d+)"))) {
      int tmp = std::stoi(m[1]);
      // read next line
      getline(infileStream, line);

      int ff;
      if ( line.find("true") != std::string::npos ){
        ff = 1;
      } else {
        ff = 0;
      }

      if (h_inst_idx.find(tmp) != h_inst_idx.end()) {
        insts[h_inst_idx.at(tmp)]->setFlipFlag(ff);
      } else {
        // InstVar *tmp_inst_var = new InstVar(tmp, -1, -1, -1, ff, -1, -1);
        std::shared_ptr<InstVar> tmp_inst_var =
            std::make_shared<InstVar>(tmp, -1, -1, -1, ff, -1, -1);
        insts.push_back(tmp_inst_var);
        h_inst_idx[tmp] = idx_inst;
        idx_inst++;
      }
    } else if (boost::regex_search(line, m,
                                   boost::regex("^.*\\(define-fun w(\\d+)"))) {
      int tmp = std::stoi(m[1]);
      // read next line
      getline(infileStream, line);
      int w;
      if (boost::regex_search(line, m, boost::regex("^    #b(\\S+)\\)"))) {
        std::string w_binary =
            boost::regex_replace(line, boost::regex("^\\s+#b(\\S+)\\)"), "$1");
        w = std::stoi(w_binary, nullptr, 2);
      } else if (boost::regex_search(line, m,
                                     boost::regex("^    #x(\\S+)\\)"))) {
        std::string w_hex =
            "0x" +
            boost::regex_replace(line, boost::regex("^\\s+#x(\\S+)\\)"), "$1");
        w = std::stoul(w_hex, nullptr, 16);
      }

      if (h_inst_idx.find(tmp) != h_inst_idx.end()) {
        insts[h_inst_idx.at(tmp)]->setWidth(w);
      } else {
        // InstVar *tmp_inst_var = new InstVar(tmp, -1, -1, -1, -1, w, -1);
        std::shared_ptr<InstVar> tmp_inst_var =
            std::make_shared<InstVar>(tmp, -1, -1, -1, -1, w, -1);
        insts.push_back(tmp_inst_var);
        h_inst_idx[tmp] = idx_inst;
        idx_inst++;
      }
    } else if (boost::regex_search(line, m,
                                   boost::regex("^.*\\(define-fun uw(\\d+)"))) {
      int tmp = std::stoi(m[1]);
      // read next line
      getline(infileStream, line);
      int uw;
      if (boost::regex_search(line, m, boost::regex("^    #b(\\S+)\\)"))) {
        std::string uw_binary =
            boost::regex_replace(line, boost::regex("^\\s+#b(\\S+)\\)"), "$1");
        uw = std::stoi(uw_binary, nullptr, 2);
      } else if (boost::regex_search(line, m,
                                     boost::regex("^    #x(\\S+)\\)"))) {
        std::string uw_hex =
            "0x" +
            boost::regex_replace(line, boost::regex("^\\s+#x(\\S+)\\)"), "$1");
        uw = std::stoul(uw_hex, nullptr, 16);
      }
      if (h_inst_idx.find(tmp) != h_inst_idx.end()) {
        insts[h_inst_idx.at(tmp)]->setUnitWidth(uw);
      } else {
        // InstVar *tmp_inst_var = new InstVar(tmp, -1, -1, -1, -1, -1, uw);
        std::shared_ptr<InstVar> tmp_inst_var =
            std::make_shared<InstVar>(tmp, -1, -1, -1, -1, -1, uw);
        insts.push_back(tmp_inst_var);
        h_inst_idx[tmp] = idx_inst;
        idx_inst++;
      }
    }

    // ### Metal Info ###
    // translate this perl code to c++ /^.*\(define-fun
    // M_m(\d+)r(\d+)c(\d+)_m(\d+)r(\d+)c(\d+)/
    if (boost::regex_search(
            line, m,
            boost::regex("^.*\\(define-fun "
                         "M_m(\\d+)r(\\d+)c(\\d+)_m(\\d+)r(\\d+)c(\\d+)"))) {
      int from_m = std::stoi(m[1]);
      int from_r = std::stoi(m[2]);
      int from_c = std::stoi(m[3]);
      int to_m = std::stoi(m[4]);
      int to_r = std::stoi(m[5]);
      int to_c = std::stoi(m[6]);

      // read next line
      getline(infileStream, line);

      // was this line used in the solution?
      int usage;
      // if (boost::regex_search(line, m, boost::regex("    (\\S+)\\)"))) {
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }

      // no need to store unused metal
      if (usage == 0) {
        continue;
      }

      // same metal layer ==> push to metal track
      if (from_m == to_m) {
        std::shared_ptr<MetalVar> tmp_metal_var =
            std::make_shared<MetalVar>(from_m, from_r, from_c, to_r, to_c);
        metals.push_back(tmp_metal_var);

        // if vertical?
        if (from_c == to_c) {
          // M1
          if (from_m == 1) {
            M1_metal_V[from_c].push_back(to_r);
            M1_metal_V[from_c].push_back(from_r);
          }
          // M3
          if (from_m == 3) {
            M3_metal_V[from_c].push_back(to_r);
            M3_metal_V[from_c].push_back(from_r);
          }
        }
        // if horizontal?
        if (from_r == to_r) {
          // M2
          if (from_m == 2) {
            M2_metal_H[from_r].push_back(to_c);
            M2_metal_H[from_r].push_back(from_c);
          }
          // M4
          if (from_m == 4) {
            M4_metal_H[from_r].push_back(to_c);
            M4_metal_H[from_r].push_back(from_c);
          }
        }

        if (to_m == 4) {
          cost_ml2 = cost_ml2 + 4;
        } else if (to_m >= 2) {
          cost_ml2++;
        }
      } else {
        std::shared_ptr<ViaVar> tmp_via_var =
            std::make_shared<ViaVar>(from_m, to_m, from_r, from_c);
        vias.push_back(tmp_via_var);
        if (to_m == 4) {
          cost_ml2 = cost_ml2 + 8;
        } else if (to_m >= 2) {
          cost_ml2 = cost_ml2 + 4;
        }
      }
    }
    // ### Wire Info ###
    if (boost::regex_search(
            line, m,
            boost::regex("^.*\\(define-fun "
                         "N(\\S+)_C(\\S+)_E_m(\\d+)r(\\d+)c(\\d+)_m("
                         "\\d+)r(\\d+)c(\\d+)"))) {
      int from_m = std::stoi(m[3]);
      int from_r = std::stoi(m[4]);
      int from_c = std::stoi(m[5]);
      int to_m = std::stoi(m[6]);
      int to_r = std::stoi(m[7]);
      int to_c = std::stoi(m[8]);

      // read next line
      getline(infileStream, line);

      // was this line used in the solution?
      int usage;
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }

      // no need to store unused wire
      if (usage == 0) {
        continue;
      }

      // WireVar *tmp_wire_var = new WireVar(from_m, to_m, from_r, from_c, to_r, to_c);
      std::shared_ptr<WireVar> tmp_wire_var =
          std::make_shared<WireVar>(from_m, to_m, from_r, from_c, to_r, to_c);

      if (h_all_wire.find(tmp_wire_var->toStr()) == h_all_wire.end()) {
        // Metal Line
        if (from_m == to_m) {
          wires.push_back(tmp_wire_var);
          if (to_m == 4) {
            cost_wl = cost_wl + 4;
          } else if (to_m >= 2) {
            cost_wl++;
          }
        } else {
          // Via
          // ViaWireVar *tmp_via_wire_var =
          //     new ViaWireVar(from_m, to_m, from_r, from_c);
          // via_wires.push_back(tmp_via_wire_var);
          std::shared_ptr<ViaWireVar> tmp_via_wire_var =
              std::make_shared<ViaWireVar>(from_m, to_m, from_r, from_c);
          via_wires.push_back(tmp_via_wire_var);
          if (to_m == 4) {
            cost_wl = cost_wl + 8;
          } else if (to_m >= 2) {
            cost_wl = cost_wl + 4;
          }
        }
        h_all_wire[tmp_wire_var->toStr()] = 1;
      }
    }

    // ### Net Info ###
    if (boost::regex_search(
            line, m,
            boost::regex(
                "^.*\\(define-fun "
                "N(\\S+)_E_m(\\d+)r(\\d+)c(\\d+)_m(\\d+)r(\\d+)c(\\d+)"))) {
      int netID = std::stoi(m[1]);
      int from_m = std::stoi(m[2]);
      int from_r = std::stoi(m[3]);
      int from_c = std::stoi(m[4]);
      int to_m = std::stoi(m[5]);
      int to_r = std::stoi(m[6]);
      int to_c = std::stoi(m[7]);

      // read next line
      getline(infileStream, line);

      // was this line used in the solution?
      int usage;
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }

      // no need to store unused net
      if (usage == 0) {
        continue;
      }

      // NetVar *tmp_net_var =
      //     new NetVar(from_m, to_m, from_r, from_c, to_r, to_c);
      std::shared_ptr<NetVar> tmp_net_var =
          std::make_shared<NetVar>(from_m, to_m, from_r, from_c, to_r, to_c);
      if (h_net.find(tmp_net_var->toStr()) == h_net.end()) {
        nets.push_back(tmp_net_var);
        // net are undirected, so generate all possible direction
        h_net[(std::make_shared<NetVar>(from_m, to_m, from_r, from_c, to_r, to_c))
                  ->toStr()] = netID;
        h_net[(std::make_shared<NetVar>(from_m, to_m, to_r, from_c, from_r, to_c))
                  ->toStr()] = netID;
        h_net[(std::make_shared<NetVar>(from_m, to_m, from_r, to_c, to_r, from_c))
                  ->toStr()] = netID;
        h_net[(std::make_shared<NetVar>(to_m, from_m, from_r, from_c, to_r, to_c))
                  ->toStr()] = netID;
      }
    }

    // ### Pin Info ###
    if (boost::regex_search(
            line, m,
            boost::regex("^.*\\(define-fun "
                         "M_.*(pin[a-zA-Z0-9_]+)_r(\\d+)c(\\d+)"))) {
      std::string pinName = m[1];
      int row = std::stoi(m[2]);
      int col = std::stoi(m[3]);
      // read next line
      getline(infileStream, line);
      // was this line used in the solution?
      int usage;
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused wire
      if (usage == 0) {
        continue;
      }
      // PinVar *tmp_pin_var = new PinVar(pinName, row, col);
      // pins.push_back(tmp_pin_var);

      std::shared_ptr<PinVar> tmp_pin_var =
          std::make_shared<PinVar>(pinName, row, col);
      pins.push_back(tmp_pin_var);
      h_pin[tmp_pin_var->toInt()] = 1;
    } else if (boost::regex_search(
                   line, m,
                   boost::regex("^.*\\(define-fun "
                                "N.*C.*m1r(\\d+)c(\\d+)_(pin[a-zA-Z0-9_]+)"))) {
      std::string pinName = m[3];
      int row = std::stoi(m[1]);
      int col = std::stoi(m[2]);
      // read next line
      getline(infileStream, line);
      // was this line used in the solution?
      int usage;
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused wire
      if (usage == 0) {
        continue;
      }
      // PinVar *tmp_pin_var = new PinVar(pinName, row, col);
      // pins.push_back(tmp_pin_var);
      
      std::shared_ptr<PinVar> tmp_pin_var =
          std::make_shared<PinVar>(pinName, row, col);
      pins.push_back(tmp_pin_var);

      h_pin[tmp_pin_var->toInt()] = 1;
    }

    // ### ExtPin Info ###
    if (boost::regex_search(
            line, m,
            boost::regex(
                "^.*\\(define-fun N(\\d+)_E_m(\\d+)r(\\d+)c(\\d+)_pinSON"))) {
      int netID = std::stoi(m[1]);
      int metal = std::stoi(m[2]);
      int row = std::stoi(m[3]);
      int col = std::stoi(m[4]);
      // read next line
      getline(infileStream, line);
      // was this line used in the solution?
      int usage;
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused wire
      if (usage == 0) {
        continue;
      }
      // ExtPinVar *tmp_extpin_var = new ExtPinVar(netID, metal, row, col);
      
      std::shared_ptr<ExtPinVar> tmp_extpin_var =
          std::make_shared<ExtPinVar>(netID, metal, row, col);

      if (h_extpin.find(tmp_extpin_var->toInt()) == h_extpin.end()) {
        extpins.push_back(tmp_extpin_var);

        h_extpin[tmp_extpin_var->toInt()] = 1;
      }
    }

    // ### Cost Info ###
    if (boost::regex_search(line, m,
                            boost::regex("^.*\\(define-fun COST_SIZE "))) {
      // read next line
      getline(infileStream, line);

      int cost;
      if (boost::regex_search(line, m, boost::regex("^    #b(\\S+)\\)"))) {
        std::string w_binary =
            boost::regex_replace(line, boost::regex("^\\s+#b(\\S+)\\)"), "$1");
        cost = std::stoi(w_binary, nullptr, 2);
      } else if (boost::regex_search(line, m,
                                     boost::regex("^    #x(\\S+)\\)"))) {
        std::string w_hex =
            "0x" +
            boost::regex_replace(line, boost::regex("^\\s+#x(\\S+)\\)"), "$1");
        cost = std::stoul(w_hex, nullptr, 16);
      }

      if (cost > cost_placement) {
        cost_placement = (cost + 2) * M1_FACTOR;
      }
    }

    // ### M2 Track Info ###
    if (boost::regex_search(line, m,
                            boost::regex("^.*\\(define-fun M4_TRACK_(\\d+)"))) {
      // int row = std::stoi(m[1]);

      // read next line
      getline(infileStream, line);

      int usage;
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused track
      if (usage == 0) {
        continue;
      }

      no_m2_tracks++;
    }

    // ### LISD Info ###
    if (boost::regex_search(line, m,
                            boost::regex("^.*\\(define-fun lisd_s(\\d+)m1c(\\d+)"))) {
      int site = std::stoi(m[1]); // site
      int col = std::stoi(m[2]);  // column
      // read next line
      int usage;
      getline(infileStream, line);
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused track
      if (usage == 0) {
        continue;
      } else {
        lisd_cols[site].push_back(col);
      }
    }

    // ### Gate Cut Info ###
    if (boost::regex_search(line, m,
                            boost::regex("^.*\\(define-fun gc_s(\\d+)m1c(\\d+)"))) {
      int site = std::stoi(m[1]); // site
      int col = std::stoi(m[2]);  // column
      // read next line
      int usage;
      getline(infileStream, line);
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused track
      if (usage == 0) {
        continue;
      } else {
        gc_cols[site].push_back(col);
      }
    }

    // ### Pass Through Info ###
    if (boost::regex_search(line, m,
                            boost::regex("^.*\\(define-fun pt_m1c(\\d+)"))) {
      int col = std::stoi(m[1]);  // column
      // read next line
      int usage;
      getline(infileStream, line);
      if ( line.find("true") != std::string::npos ){
        usage = 1;
      } else {
        usage = 0;
      }
      // no need to store unused track
      if (usage == 0) {
        continue;
      } else {
        pass_throughs.push_back(col);
      }
    }
  }


  fmt::print("a     [INFO] Reading Result Done. Start to Merge Vertices ...\n");
  // Merge into metal segaments into metals if they are adjacent
  // Using Klee's Algorithm to achieve stepsize-free merging
  // vertical metals
  for (auto m1_metal_segment : M1_metal_V) {
    int col = m1_metal_segment.first;
    std::vector<int> segments = m1_metal_segment.second;
    std::sort(segments.begin(), segments.end());
    int prev_row = -1;
    int curr_row = -1;
    int start_row = -1;
    int net_id = -1;
    bool if_check_merge = false; // only check merge if in between two segments

    for (std::size_t i = 0; i < segments.size(); i++) {
      if (i == 0) {
        prev_row = segments[i];
        curr_row = segments[i];
        start_row = segments[i];
        int next_row = segments[i + 1]; // temp value to retrieve net_id
        // net_id = h_net.at(fmt::format("1_1_{}_{}_{}_{}", start_row, col,
        //                                next_row, col));
        // check if h_net has this key first
        if (h_net.find(fmt::format("1_1_{}_{}_{}_{}", start_row, col, next_row, col)) == h_net.end()) {
          fmt::print("a     [ERROR] Cannot find key: 1_1_{}_{}_{}_{}\n", start_row, col, next_row, col);
          net_id = -1;
        } else {
          net_id = h_net.at(fmt::format("1_1_{}_{}_{}_{}", start_row, col, next_row, col));
        }
        // net_id = h_net.at(MetalVar(1, start_row, col, next_row, col).toInt());
        if_check_merge = false;
      } else if (i == segments.size() - 1) {
        // set rows
        prev_row = curr_row;
        curr_row = segments[i];

        // merge whatever is left
        // MetalVar *tmp_metal_var =
        //     new MetalVar(1, start_row, col, curr_row, col, net_id);
        // final_metal.push_back(tmp_metal_var);

        std::shared_ptr<MetalVar> tmp_metal_var =
            std::make_shared<MetalVar>(1, start_row, col, curr_row, col, net_id);
        final_metal.push_back(tmp_metal_var);
      } else {
        // set rows
        prev_row = curr_row;
        curr_row = segments[i];
        int next_row = segments[i + 1]; // temp value to retrieve net_id

        // check if merge
        if (if_check_merge) {
          if (prev_row == curr_row) {
            // merge
          } else {
            // no merge, new segment added to final metal
            // MetalVar *tmp_metal_var =
            //     new MetalVar(1, start_row, col, prev_row, col, net_id);
            // final_metal.push_back(tmp_metal_var);

            std::shared_ptr<MetalVar> tmp_metal_var =
                std::make_shared<MetalVar>(1, start_row, col, prev_row, col, net_id);
            final_metal.push_back(tmp_metal_var);
            // set new start_row
            start_row = curr_row;
            // set new net_id
            // net_id = h_net.at(fmt::format("1_1_{}_{}_{}_{}", start_row, col,
            //                                next_row, col));
            if (h_net.find(fmt::format("1_1_{}_{}_{}_{}", start_row, col, next_row, col)) == h_net.end()) {
              fmt::print("a     [ERROR] Cannot find key: 1_1_{}_{}_{}_{}\n", start_row, col, next_row, col);
              net_id = -1;
            } else {
              net_id = h_net.at(fmt::format("1_1_{}_{}_{}_{}", start_row, col, next_row, col));
            }
            // net_id =
            //     h_net.at(MetalVar(1, start_row, col, next_row, col).toInt());
          }
        }
        // flip this flag
        if_check_merge = !if_check_merge;
      }
    }
  }

  // horizontal metals
  for (auto m2_metal_segment : M2_metal_H) {
    int row = m2_metal_segment.first;
    std::vector<int> segments = m2_metal_segment.second;
    std::sort(segments.begin(), segments.end());
    int prev_col = -1;
    int curr_col = -1;
    int start_col = -1;
    int net_id = -1;
    bool if_check_merge = false; // only check merge if in between two segments

    for (std::size_t i = 0; i < segments.size(); i++) {
      if (i == 0) {
        prev_col = segments[i];
        curr_col = segments[i];
        start_col = segments[i];
        int next_col = segments[i + 1]; // temp value to retrieve net_id

        // net_id = h_net.at(fmt::format("2_2_{}_{}_{}_{}", row, start_col, row,
        //                                next_col));
        if (h_net.find(fmt::format("2_2_{}_{}_{}_{}", row, start_col, row, next_col)) == h_net.end()) {
          fmt::print("a     [ERROR] Cannot find key: 2_2_{}_{}_{}_{}\n", row, start_col, row, next_col);
          net_id = -1;
        } else {
          net_id = h_net.at(fmt::format("2_2_{}_{}_{}_{}", row, start_col, row, next_col));
        }
        // net_id = h_net.at(MetalVar(2, row, start_col, row, next_col).toInt());
        if_check_merge = false;
      } else if (i == segments.size() - 1) {
        // set cols
        prev_col = curr_col;
        curr_col = segments[i];

        // merge whatever is left
        // MetalVar *tmp_metal_var =
        //     new MetalVar(2, row, start_col, row, curr_col, net_id);
        // final_metal.push_back(tmp_metal_var);

        std::shared_ptr<MetalVar> tmp_metal_var =
            std::make_shared<MetalVar>(2, row, start_col, row, curr_col, net_id);
        final_metal.push_back(tmp_metal_var);
      } else {
        // set cols
        prev_col = curr_col;
        curr_col = segments[i];
        int next_col = segments[i + 1]; // temp value to retrieve net_id

        // check if merge
        if (if_check_merge) {
          if (prev_col == curr_col) {
            // merge
          } else {
            // no merge, new segment added to final metal
            // MetalVar *tmp_metal_var =
            //     new MetalVar(2, row, start_col, row, prev_col, net_id);
            // final_metal.push_back(tmp_metal_var);

            std::shared_ptr<MetalVar> tmp_metal_var =
                std::make_shared<MetalVar>(2, row, start_col, row, prev_col, net_id);
            final_metal.push_back(tmp_metal_var);
            // set new start_col
            start_col = curr_col;
            // set new net_id
            // net_id = h_net.at(fmt::format("2_2_{}_{}_{}_{}", row, start_col, row,
            //                                next_col));
            if (h_net.find(fmt::format("2_2_{}_{}_{}_{}", row, start_col, row, next_col)) == h_net.end()) {
              fmt::print("a     [ERROR] Cannot find key: 2_2_{}_{}_{}_{}\n", row, start_col, row, next_col);
              net_id = -1;
            } else {
              net_id = h_net.at(fmt::format("2_2_{}_{}_{}_{}", row, start_col, row, next_col));
            }
            // net_id = h_net.at(
            //     MetalVar(2, row, start_col, row, next_col).toInt());
          }
        }
        // flip this flag
        if_check_merge = !if_check_merge;
      }
    }
  }

  for (auto m3_metal_segment : M3_metal_V) {
    int col = m3_metal_segment.first;
    std::vector<int> segments = m3_metal_segment.second;
    std::sort(segments.begin(), segments.end());
    int prev_row = -1;
    int curr_row = -1;
    int start_row = -1;
    int net_id = -1;
    bool if_check_merge = false; // only check merge if in between two segments

    for (std::size_t i = 0; i < segments.size(); i++) {
      if (i == 0) {
        prev_row = segments[i];
        curr_row = segments[i];
        start_row = segments[i];
        int next_row = segments[i + 1]; // temp value to retrieve net_id

        // net_id = h_net.at(fmt::format("3_3_{}_{}_{}_{}", start_row, col,
        //                                next_row, col));
        if (h_net.find(fmt::format("3_3_{}_{}_{}_{}", start_row, col, next_row, col)) == h_net.end()) {
          fmt::print("a     [ERROR] Cannot find key: 3_3_{}_{}_{}_{}\n", start_row, col, next_row, col);
          net_id = -1;
        } else {
          net_id = h_net.at(fmt::format("3_3_{}_{}_{}_{}", start_row, col, next_row, col));
        }
        // net_id =
        //     h_net.at(MetalVar(3, start_row, col, next_row, col).toInt());
        if_check_merge = false;
      } else if (i == segments.size() - 1) {
        // set rows
        prev_row = curr_row;
        curr_row = segments[i];

        // merge whatever is left
        // MetalVar *tmp_metal_var =
        //     new MetalVar(3, start_row, col, curr_row, col, net_id);
        // final_metal.push_back(tmp_metal_var);

        std::shared_ptr<MetalVar> tmp_metal_var =
            std::make_shared<MetalVar>(3, start_row, col, curr_row, col, net_id);
        final_metal.push_back(tmp_metal_var);
      } else {
        // set rows
        prev_row = curr_row;
        curr_row = segments[i];
        int next_row = segments[i + 1]; // temp value to retrieve net_id

        // check if merge
        if (if_check_merge) {
          if (prev_row == curr_row) {
            // merge
          } else {
            // no merge, new segment added to final metal
            // MetalVar *tmp_metal_var =
            //     new MetalVar(3, start_row, col, prev_row, col, net_id);
            // final_metal.push_back(tmp_metal_var);

            std::shared_ptr<MetalVar> tmp_metal_var =
                std::make_shared<MetalVar>(3, start_row, col, prev_row, col, net_id);
            final_metal.push_back(tmp_metal_var);
            // set new start_row
            start_row = curr_row;

            // set new net_id
            // net_id = h_net.at(fmt::format("3_3_{}_{}_{}_{}", start_row, col,
            //                                next_row, col));
            if (h_net.find(fmt::format("3_3_{}_{}_{}_{}", start_row, col, next_row, col)) == h_net.end()) {
              fmt::print("a     [ERROR] Cannot find key: 3_3_{}_{}_{}_{}\n", start_row, col, next_row, col);
              net_id = -1;
            } else {
              net_id = h_net.at(fmt::format("3_3_{}_{}_{}_{}", start_row, col, next_row, col));
            }

            // net_id = h_net.at(
            //     MetalVar(3, start_row, col, next_row, col).toInt());
          }
        }
        // flip this flag
        if_check_merge = !if_check_merge;
      }
    }
  }

  for (auto m4_metal_segment : M4_metal_H) {
    int row = m4_metal_segment.first;
    std::vector<int> segments = m4_metal_segment.second;
    std::sort(segments.begin(), segments.end());
    int prev_col = -1;
    int curr_col = -1;
    int start_col = -1;
    int net_id = -1;
    bool if_check_merge = false; // only check merge if in between two segments

    for (std::size_t i = 0; i < segments.size(); i++) {
      if (i == 0) {
        prev_col = segments[i];
        curr_col = segments[i];
        start_col = segments[i];
        int next_col = segments[i + 1]; // temp value to retrieve net_id

        // net_id = h_net.at(fmt::format("4_4_{}_{}_{}_{}", row, start_col, row,
        //                                next_col));
        if (h_net.find(fmt::format("4_4_{}_{}_{}_{}", row, start_col, row, next_col)) == h_net.end()) {
          fmt::print("a     [ERROR] Cannot find key: 4_4_{}_{}_{}_{}\n", row, start_col, row, next_col);
          net_id = -1;
        } else {
          net_id = h_net.at(fmt::format("4_4_{}_{}_{}_{}", row, start_col, row, next_col));
        }
        // net_id =
        //     h_net.at(MetalVar(4, row, start_col, row, next_col).toInt());
        if_check_merge = false;
      } else if (i == segments.size() - 1) {
        // set cols
        prev_col = curr_col;
        curr_col = segments[i];

        // merge whatever is left
        // MetalVar *tmp_metal_var =
        //     new MetalVar(4, row, start_col, row, curr_col, net_id);
        // final_metal.push_back(tmp_metal_var);

        std::shared_ptr<MetalVar> tmp_metal_var =
            std::make_shared<MetalVar>(4, row, start_col, row, curr_col, net_id);
        final_metal.push_back(tmp_metal_var);
      } else {
        // set cols
        prev_col = curr_col;
        curr_col = segments[i];
        int next_col = segments[i + 1]; // temp value to retrieve net_id

        // check if merge
        if (if_check_merge) {
          if (prev_col == curr_col) {
            // merge
          } else {
            // no merge, new segment added to final metal
            // MetalVar *tmp_metal_var =
            //     new MetalVar(4, row, start_col, row, prev_col, net_id);
            // final_metal.push_back(tmp_metal_var);

            std::shared_ptr<MetalVar> tmp_metal_var =
                std::make_shared<MetalVar>(4, row, start_col, row, prev_col, net_id);
            final_metal.push_back(tmp_metal_var);
            // set new start_col
            start_col = curr_col;

            // set new net_id
            // net_id = h_net.at(fmt::format("4_4_{}_{}_{}_{}", row, start_col, row,
            //                                next_col));
            if (h_net.find(fmt::format("4_4_{}_{}_{}_{}", row, start_col, row, next_col)) == h_net.end()) {
              fmt::print("a     [ERROR] Cannot find key: 4_4_{}_{}_{}_{}\n", row, start_col, row, next_col);
              net_id = -1;
            } else {
              net_id = h_net.at(fmt::format("4_4_{}_{}_{}_{}", row, start_col, row, next_col));
            }
          }
        }
        // flip this flag
        if_check_merge = !if_check_merge;
      }
    }
  }

  for (std::size_t i = 0; i < vias.size(); i++) {
    final_via.push_back(vias[i]);
  }

  fmt::print("a     [INFO] Merge Vertices Done. Start to writing to output ...\n");

  // ### print result ###
  auto tmp = infile.substr(infile.rfind("/") + 1);
  outfile = outdir / tmp.substr(0, tmp.find(".")).append(".conv");

  std::FILE *out = std::fopen(outfile.c_str(), "w");
  fmt::print(out, "COST {} {} {}\n", cost_placement, cost_ml, cost_wl);
  fmt::print(out, "TRACK {} {}\n", numTrackV, numTrackH * 2 + 2);

  for (std::size_t i = 0; i < insts.size(); i++) {
    fmt::print(out, insts[i]->dump());
  }

  for (std::size_t i = 0; i < pins.size(); i++) {
    fmt::print(out, pins[i]->dump());
  }

  // print metal by ascending layer orders
  for (std::size_t i = 0; i < final_metal.size(); i++) {
    fmt::print(out, final_metal[i]->dump());
  }

  // print wires and via wires by ascending layer orders
  // these variables tend to be ignored as they are for debug purpose on nets
  for (std::size_t i = 0; i < wires.size(); i++) {
    if (wires[i]->metalID == 1) {
      fmt::print(out, wires[i]->dump());
    }
  }

  for (std::size_t i = 0; i < via_wires.size(); i++) {
    if (via_wires[i]->fromMetal == 1 && via_wires[i]->toMetal == 2) {
      fmt::print(out, via_wires[i]->dump());
    } else if (via_wires[i]->fromMetal == 2 && via_wires[i]->toMetal == 1) {
      fmt::print(out, via_wires[i]->dump());
    }
  }

  for (std::size_t i = 0; i < wires.size(); i++) {
    if (wires[i]->metalID == 2) {
      fmt::print(out, wires[i]->dump());
    }
  }

  for (std::size_t i = 0; i < via_wires.size(); i++) {
    if (via_wires[i]->fromMetal == 2 && via_wires[i]->toMetal == 3) {
      fmt::print(out, via_wires[i]->dump());
    } else if (via_wires[i]->fromMetal == 3 && via_wires[i]->toMetal == 2) {
      fmt::print(out, via_wires[i]->dump());
    }
  }

  for (std::size_t i = 0; i < wires.size(); i++) {
    if (wires[i]->metalID == 3) {
      fmt::print(out, wires[i]->dump());
    }
  }

  for (std::size_t i = 0; i < via_wires.size(); i++) {
    if (via_wires[i]->fromMetal == 3 && via_wires[i]->toMetal == 4) {
      fmt::print(out, via_wires[i]->dump());
    } else if (via_wires[i]->fromMetal == 4 && via_wires[i]->toMetal == 3) {
      fmt::print(out, via_wires[i]->dump());
    }
  }

  for (std::size_t i = 0; i < wires.size(); i++) {
    if (wires[i]->metalID == 4) {
      fmt::print(out, wires[i]->dump());
    }
  }
  // these variables tend to be ignored as they are for debug purpose on nets
  for (std::size_t i = 0; i < vias.size(); i++) {
    fmt::print(out, vias[i]->dump(h_net.at(vias[i]->getNetIndex())));
  }
  // print external pins
  for (std::size_t i = 0; i < extpins.size(); i++) {
    fmt::print(out, extpins[i]->dump(h_extpin_name.at(extpins[i]->netID),
                                     h_extpin_type.at(extpins[i]->netID)));
  }
  // append LISD
  for (std::size_t i = 0; i < lisd_cols.size(); i++) {
    std::sort(lisd_cols[i].begin(), lisd_cols[i].end());
    for (std::size_t j = 0; j < lisd_cols[i].size(); j++) {
      fmt::print(out, "LISD {} {}\n", i, lisd_cols[i][j]);
    }
  }
  // append GCut
  for (std::size_t i = 0; i < gc_cols.size(); i++) {
    std::sort(gc_cols[i].begin(), gc_cols[i].end());
    for (std::size_t j = 0; j < gc_cols[i].size(); j++) {
      fmt::print(out, "GC {} {}\n", i, gc_cols[i][j]);
    }
  }
  // append PassThrough
  for (std::size_t i = 0; i < pass_throughs.size(); i++) {
    fmt::print(out, "PT {}\n", pass_throughs[i]);
  }

  infileStream.close();
  pinLayoutfileStream.close();
  std::fclose(out);

  fmt::print("a     [INFO] Converting Result Completed!\n Output File: {}\n",
             outfile);
}