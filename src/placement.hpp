#define FMT_HEADER_ONLY
#pragma once
#define FMT_HEADER_ONLY
#include <boost/multiprecision/integer.hpp> // for returning bit length
#include <fmt/core.h>
#include <fmt/format.h>
#include <iostream>
#include <map>
#include <regex>
#include <string>
#include <vector>

class Placement {
public:
  // COST_SIZE, COST_SIZE_P, COST_SIZE_N, M4_TRACK_#...
  void init_cost_var(FILE *fp);

  void fix_placement(FILE *fp);

  void init_lisd_col_var(FILE *fp);

  void write_lisd_col_has_only_one_connection();

  void write_lisd_col_has_pin_alignment_or_empty_space();

  void init_gcut_col_var(FILE *fp);

  void init_pass_through_col_var(FILE *fp);

  void write_pass_through_col(int gate_passthrough, int sd_passthrough);

  void write_pass_through_col_has_gate_pin_alignment(std::string order_clip);

  void write_pass_through_col_has_sd_pin_alignment(std::string order_clip);

  void write_gate_cut_with_two_cb_condition();

  void write_prohibit_gate_connection(int min_cpp);

  void write_prohibit_middle_gate_connection();

  void write_limit_lisd_gc_pt_var_by_cost_size();

  // define max subroutine
  void write_max_func(FILE *fp);

  // instance placement info: x#, y# ...
  void write_placement_var(FILE *fp);

  // placable range
  void write_placement_range_constr(FILE *fp);

  // placement variables
  void set_placement_var_pmos(FILE *fp);

  void set_placement_var_nmos(FILE *fp);

  // set G on even columns and S/D on odd columns
  void set_placement_legal_col(FILE *fp);

  // SDB/DDB
  void write_XOL(FILE *fp, bool ifPMOS, int XOL_Mode, int NDE_Parameter,
                 int XOL_Parameter);

  void remove_x_symmetric_placement(FILE *fp, bool BS_Parameter);

  void remove_y_symmetric_placement(FILE *fp, bool BS_Parameter);

  void set_default_G_metal();

  void unset_rightmost_metal();

  void localize_adjacent_pin(int local_Parameter);

  void init_placement_G_pin(std::string order_clip);

  void init_placement_SD_pin(std::string order_clip);

  // # Generating Instance Group Array
  void init_inst_partition(int Partition_Parameter);

  void write_partition_constraint(int Partition_Parameter);

  void write_cost_func_mos(FILE *fp);

  void write_cost_func(FILE *fp, int Partition_Parameter);

  void write_top_metal_track_usage(FILE *fp);

  void write_top_metal_offset(FILE *fp);

  void write_pin_partition(FILE *fp);

  void write_instance_alignment(FILE *fp);

  void write_minimize_cost_func(FILE *fp, int Partition_Parameter, bool ifMinimizeM4);

  void write_minimize_via_cost(FILE *fp);

  void write_bound_horizontal_track_width(FILE *fp);
};