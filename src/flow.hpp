#define FMT_HEADER_ONLYget_n
#include <fmt/core.h>
#include <fmt/format.h>
#include <boost/regex.hpp>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>
#include <regex>

/*
  [09/24/2024] Added write_bind_edge_commodity to avoid floating M0 issue.
*/

class FlowWriter {
public:
  void init_commodity_flow_var();
  void localize_commodity(int local_Parameter, int tolerance_Parameter);

  std::string localize_commodity_helper(int col, int commodityIndex, int netIndex);

  // Flow Capacity Control
  void write_flow_capacity_control();
  void flow_indicator_helper(std::string pidx, int netIndex, int commodityIndex);

  // Part 1
  void write_flow_conservation(FILE *fp, int EXT_Parameter);

  // Part 2
  void write_vertex_exclusive_placement_passthrough(FILE *fp);
  void write_vertex_exclusive_routing(FILE *fp);

  // Part 3
  void write_edge_assignment(FILE *fp);
  void write_bind_edge_commodity(FILE *fp);

  // Part 4
  void write_edge_exclusive(FILE *fp);

  // Part 11
  void write_net_consistency();

  // Legal FLAG : for external cell abutment
  void disable_cell_boundary();
};