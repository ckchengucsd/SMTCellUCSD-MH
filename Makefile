################################################
# Tool config                                  #
################################################
# python
PYTHON=$(shell which python3)

# Z3 (4.11.2)
Z3=$(shell which z3)
Z3FLAGS=parallel.enable=true -T:18000

# Klayout
KLAYOUT=$(shell which klayout)

# GDT to GDS
GDT2GDS=$(shell which gdt2gds.Linux)

# Misc
RM=rm -rf
TIME=time

# C++ compiler
CXX=g++
FILESYS=-lstdc++fs
CPPFLAGS=-std=c++17

################################################
# Input config                                 #
################################################
# PNNP Cell
CELL_NAME = BUF_X4Tr6 BUF_X8Tr6 MUX2_X1\
AND2_X2Tr8 AND3_X2Tr10 AOI21_X1 AOI21_X2Tr12 AOI22_X2Tr16 AOI22_X1 OAI21_X1\
NAND2_X1 NAND2_X2Tr8 NAND3_X1 NAND3_X2Tr12 NAND4_X1 NAND4_X2Tr16\
LHQ_X1 DFFHQNEQFIN_X1
# NPPN Cell
CELL_NAME = BUF_X4Tr6 BUF_X8Tr6 MUX2_X1\
NOR2_X1 NOR3_X1 NOR2_X2Tr8 NOR3_X2Tr12 NOR4_X1 NOR4_X2Tr16\
OAI21_X1 OAI21_X2Tr12 OAI22_X1 OAI22_X2Tr16 OR2_X2Tr8 OR3_X2Tr10 XOR2_X1\
LHQ_X1 DFFHQNEQFIN_X1
CONFIG=./config/config_2F_4T_4530_OF0_MH_NPPN.json # Change this to the config file you want to use
UTIL_CONFIG=./util/check_config.py

# GDS/LEF config
FIN 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) NumFin)
TRACK 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) NumTrack)
CHSTR 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) CHSTR)
SITE_NAME 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) SiteName)
OrderClip 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) OrderClip)
SD_PASSTHRU := $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) SD_PASSTHROUGH)
G_PASSTHRU 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) GATE_PASSTHROUGH)
M1_MPO 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M1_MPO_Parameter)
PGPIN 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) PGPIN)
DR 			:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) DR)
CPP 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) CPP)
M1_Factor 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M1_Factor)
M0P 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M0P)
M2_Factor 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M2_Factor)
M1P 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M1P)
M3_Factor 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M3_Factor)
M3_Offset	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M3_Offset)
M2P 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M2P)
M4_Factor 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M4_Factor)
ENC 		:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) ENC)
FINWIDTH 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) FinWidth)
FINPITCH 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) FinPitch)
GATEWIDTH 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) GateWidth)
M0WIDTH 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M0Width)
M1WIDTH 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M1Width)
M2WIDTH 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) M2Width)
MH_PARAM 	:= $(shell $(PYTHON) $(UTIL_CONFIG) $(CONFIG) MH_Parameter)
LIB_NAME 	:= $(CHSTR)T_$(FIN)F_$(CPP)CPP_$(M0P)M0P_$(M1P)M1P_$(M2P)M2P_$(M1_MPO)MPO_$(DR)_$(PGPIN)

################################################
# Output config                                #
################################################
RESULTS_DIR=./results/results_$(FIN)F$(TRACK)T_$(CPP)$(M1P)_OF$(M3_Offset)_$(SD_PASSTHRU)_$(G_PASSTHRU)_$(OrderClip)
LOG_DIR=$(RESULTS_DIR)/logs

################################################
# Commands generating executable files         #
# ##############################################
genSMTInput=./build/genSMTInput
convSMTResult=./build/convSMTResult

################################################
# Commands to run SMTCell flow                 #
################################################
# basic flow
SMTCell:
	mkdir -m 777 -p $(RESULTS_DIR)/inputSMT
	mkdir -m 777 -p $(RESULTS_DIR)/Z3
	mkdir -m 777 -p $(RESULTS_DIR)/time
	mkdir -m 777 -p $(RESULTS_DIR)/solutionSMT
	mkdir -m 777 -p $(RESULTS_DIR)/logs
	mkdir -m 777 -p $(RESULTS_DIR)/logs/debug
	$(foreach CELL,$(CELL_NAME),\
		$(genSMTInput) ./inputPinLayouts/pinLayouts_$(FIN)F_$(TRACK)T/$(CELL).pinLayout $(CONFIG) $(RESULTS_DIR);\
		$(TIME) -o $(RESULTS_DIR)/time/$(CELL)_DTE_$(Z3VER).log $(Z3) $(Z3FLAGS) $(RESULTS_DIR)/inputSMT/$(CELL)_$(FIN)F_$(TRACK)T.smt2 > $(RESULTS_DIR)/Z3/$(CELL)_$(FIN)F_$(TRACK)T.z3;\
		$(PYTHON) ./util/check_sat.py $(RESULTS_DIR)/Z3/$(CELL)_$(FIN)F_$(TRACK)T.z3;\
		$(convSMTResult) $(RESULTS_DIR)/Z3/$(CELL)_$(FIN)F_$(TRACK)T.z3 $(CELL) $(RESULTS_DIR)/solutionSMT ./inputPinLayouts/pinLayouts_$(FIN)F_$(TRACK)T/$(CELL).pinLayout $(M1_Factor) $(M3_Factor);)
	mkdir -m 777 -p $(RESULTS_DIR)/gdslef
	mkdir -m 777 -p $(RESULTS_DIR)/gdslef/$(LIB_NAME)
	$(PYTHON) ./util/LayoutGen_$(FIN)F$(TRACK)T_$(PGPIN)/genGdsLef.py $(RESULTS_DIR)/solutionSMT $(RESULTS_DIR)/gdslef $(M1P) $(M2P) $(CPP) $(ENC) $(SITE_NAME) $(M1_MPO) $(DR) best 0 0 $(FINWIDTH) $(FINPITCH) $(GATEWIDTH) $(M0WIDTH) $(M1WIDTH) $(M2WIDTH) $(M1_Factor) $(M3_Factor) $(MH_PARAM) $(OrderClip)
	$(GDT2GDS) < $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).gdt > $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).gds
	$(PYTHON) ./util/genLEF.py $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).gdt $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).lef
	$(foreach CELL,$(CELL_NAME),\
		$(PYTHON) ./util/extract_cell.py $(RESULTS_DIR)/solutionSMT/$(CELL)_$(FIN)F_$(TRACK)T.conv $(CPP);)

viewSMTCell:
	$(PYTHON) ./util/LayoutGen_$(FIN)F$(TRACK)T_$(PGPIN)/genGdsLef.py $(RESULTS_DIR)/solutionSMT $(RESULTS_DIR)/gdslef $(M1P) $(M2P) $(CPP) $(ENC) $(SITE_NAME) $(M1_MPO) $(DR) best 0 0 $(FINWIDTH) $(FINPITCH) $(GATEWIDTH) $(M0WIDTH) $(M1WIDTH) $(M2WIDTH) $(M1_Factor) $(M3_Factor) $(MH_PARAM) $(OrderClip)
	$(GDT2GDS) < $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).gdt > $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).gds
	$(KLAYOUT) $(RESULTS_DIR)/gdslef/$(LIB_NAME)/$(LIB_NAME).gds