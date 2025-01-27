import os
import sys
import re

"""
M0 Pins
b{15 xy(0.0125 0.0530 0.2125 0.0530 0.2125 0.0670 0.0125 0.0670)}
llx=float(floats[1]),
lly=float(floats[2]),
urx=float(floats[3]),
ury=float(floats[-1]),
t{15 tt251 mc m0.05 xy(0.1125 0.1440) 'VDD'}

M1 Pins
b{19 xy(0.0825 0.0720 0.0975 0.0720 0.0975 0.0240 0.0825 0.0240)}
t{19 tt251 mc m0.05 xy(0.1800 0.0720) 'A2'}
"""


class Cell:
    def __init__(self, *args, **kwargs):
        self.cell_name = kwargs.get("cell_name", None)
        self.pin_list = kwargs.get("pin_list", None)
        self.obs_list = kwargs.get("obs_list", None)
        self.pwr_pin_list = kwargs.get("pwr_pin_list", None)
        self.cell_width = kwargs.get("cell_width", 0.0)
        self.cell_height = kwargs.get("cell_height", 0.0)

    def set_cell_name(self, cell_name):
        self.cell_name = cell_name

    def set_pin_list(self, pin_list):
        self.pin_list = pin_list

    def set_obs_list(self, obs_list):
        self.obs_list = obs_list

    def set_pwr_pin_list(self, pwr_pin_list):
        self.pwr_pin_list = pwr_pin_list

    def set_cell_width(self, cell_width):
        self.cell_width = cell_width

    def set_cell_height(self, cell_height):
        self.cell_height = cell_height

    def add_pin(self, pin):
        self.pin_list.append(pin)

    def add_obs(self, obs):
        self.obs_list.append(obs)

    def add_pwr_pin(self, pwr_pin):
        self.pwr_pin_list.append(pwr_pin)

    def write_LEF(self, f):
        f.write("MACRO " + self.cell_name + "\n")
        f.write("  CLASS CORE ;\n")
        f.write("  ORIGIN 0 0 ;\n")
        f.write("  FOREIGN " + self.cell_name + " 0 0 ;\n")
        f.write(
            "  SIZE "
            + str(format(self.cell_width, ".4f"))
            + " BY "
            + str(format(self.cell_height, ".4f"))
            + " ;\n"
        )
        f.write("  SYMMETRY X Y ;\n")
        f.write("  SITE coresite ;\n")
        # write pins
        for pin in self.pin_list:
            # if pin name does not end with _attached, then it is a regular pin
            if not pin.pin_name.endswith("_attached"):
                pin.write_LEF(f)
        # write pwr pins
        for pwr_pin in self.pwr_pin_list:
            pwr_pin.write_LEF(f, if_pwr_pin=True)
        # write obs
        self.obs_list.write_LEF(f)
        f.write("END " + self.cell_name + "\n")


class Point:
    list_of_points = []

    def __init__(self, list_of_points_):
        self.list_of_points = list_of_points_

    def get_list_of_x(self):
        # every other element is x
        return self.list_of_points[::2]

    def get_list_of_y(self):
        # every other element is y
        return self.list_of_points[1::2]

    def get_ux(self):
        return max(self.get_list_of_x())

    def get_uy(self):
        return max(self.get_list_of_y())

    def get_lx(self):
        return min(self.get_list_of_x())

    def get_ly(self):
        return min(self.get_list_of_y())


class Pin:
    signal_direction_dict = {
        "A": "INPUT",
        "A1": "INPUT",
        "A2": "INPUT",
        "A3": "INPUT",
        "A4": "INPUT",
        "B": "INPUT",
        "B1": "INPUT",
        "B2": "INPUT",
        "B3": "INPUT",
        "B4": "INPUT",
        "CLK": "INPUT",
        "CK": "INPUT",
        "D": "INPUT",
        "E": "INPUT",
        "I": "INPUT",
        "I0": "INPUT",
        "I1": "INPUT",
        "S": "INPUT",
        "QN": "OUTPUT",
        "Q": "OUTPUT",
        "RN": "INPUT",
        "R": "INPUT",
        "Z": "OUTPUT",
        "ZN": "OUTPUT",
        "VDD": "INOUT",
        "VSS": "INOUT",
    }

    power_use_dict = {
        "VDD": "POWER",
        "VSS": "GROUND",
    }

    def __init__(self, *args, **kwargs):
        self.pin_name = kwargs.get("pin_name", None)
        self.llx = kwargs.get("llx", 0.0)
        self.lly = kwargs.get("lly", 0.0)
        self.urx = kwargs.get("urx", 0.0)
        self.ury = kwargs.get("ury", 0.0)
        self.layer = kwargs.get("layer", None)
        self.attached_pin = {}  # {layer: [via_pin]}

    def set_pin_name(self, pin_name):
        self.pin_name = pin_name

    def set_coordinates(self, llx, lly, urx, ury, layer):
        self.llx = llx
        self.lly = lly
        self.urx = urx
        self.ury = ury

    def set_layer(self, layer):
        self.layer = layer

    def if_pin_within_bbox(self, text_x, text_y):
        if (
            (text_x >= self.llx)
            and (text_x <= self.urx)
            and (text_y >= self.lly)
            and (text_y <= self.ury)
        ):
            return True
        else:
            return False

    def if_via_within_bbox(self, via_pin):
        # via_pin is a Pin object
        if (
            (via_pin.llx >= self.llx)
            and (via_pin.urx <= self.urx)
            and (via_pin.lly >= self.lly)
            and (via_pin.ury <= self.ury)
        ):
            # add the via pin to the attached_pin dict
            if via_pin.layer in self.attached_pin.keys():
                self.attached_pin[via_pin.layer].append(via_pin)
            else:
                self.attached_pin[via_pin.layer] = [via_pin]
            return True
        else:
            return False

    def if_metal_pin_connected_to_via(self, metal_pin):
        # metal_pin is a Pin object
        # if layer is M1, check if metal_pin is on M0 and is connected to a V0 via
        if self.layer == "M1":
            if metal_pin.layer == "M0":
                # if V0 is a key in the attached_pin dict
                if "V0" in self.attached_pin.keys():
                    for via_pin in self.attached_pin["V0"]:
                        # metal_pin is connected to a V0 via
                        if metal_pin.if_via_within_bbox(via_pin):
                            # assign a pin name to the metal pin
                            if self.pin_name == None:
                                metal_pin.set_pin_name("unknown_attached")
                            else:
                                metal_pin.set_pin_name(self.pin_name + "_attached")
                            # add metal_pin to the attached_pin dict
                            if metal_pin.layer in self.attached_pin.keys():
                                self.attached_pin[metal_pin.layer].append(metal_pin)
                            else:
                                self.attached_pin[metal_pin.layer] = [metal_pin]
                            return True
                # V0 via not found
                else:
                    return False
            # metal_pin is not on M0
            else:
                return False
        # if layer is M2, check if metal_pin is on M1 and is connected to a V1 via
        elif self.layer == "M2" and self.pin_name != None:
            if metal_pin.layer == "M1":
                # if V1 is a key in the attached_pin dict
                if "V1" in self.attached_pin.keys():
                    for via_pin in self.attached_pin["V1"]:
                        # metal_pin is connected to a V1 via
                        if metal_pin.if_via_within_bbox(via_pin):
                            # assign a pin name to the metal pin
                            metal_pin.set_pin_name(self.pin_name + "_attached")
                            # add metal_pin to the attached_pin dict
                            if metal_pin.layer in self.attached_pin.keys():
                                self.attached_pin[metal_pin.layer].append(metal_pin)
                            else:
                                self.attached_pin[metal_pin.layer] = [metal_pin]
                            # also add the M0 metal pin to the attached_pin dict
                            if "M0" in metal_pin.attached_pin.keys():
                                for m0_metal in metal_pin.attached_pin["M0"]:
                                    m0_metal.set_pin_name(self.pin_name + "_attached")
                                    if m0_metal.layer in self.attached_pin.keys():
                                        self.attached_pin[m0_metal.layer].append(
                                            m0_metal
                                        )
                                    else:
                                        self.attached_pin[m0_metal.layer] = [m0_metal]
                            return True
                # V1 via not found
                else:
                    return False

    def write_LEF(self, f, if_pwr_pin=False):
        f.write("  PIN " + self.pin_name + "\n")
        f.write(f"    DIRECTION {Pin.signal_direction_dict[self.pin_name]} ;\n")
        (
            f.write(f"    USE {Pin.power_use_dict[self.pin_name]} ;\n")
            if if_pwr_pin
            else f.write("    USE SIGNAL ;\n")
        )
        f.write("    SHAPE ABUTMENT ;\n") if if_pwr_pin else None
        f.write("    PORT\n")
        f.write("      LAYER " + self.layer + " ;\n")
        # with three decimal places
        if if_pwr_pin:
            f.write(
                "        RECT "
                + str(format(self.llx, ".4f"))
                + " "
                + str(format(self.lly, ".4f"))
                + " "
                + str(format(self.urx, ".4f"))
                + " "
                + str(format(self.ury, ".4f"))
                + " ;\n"
            )
        else:
            f.write(
                "        RECT "
                + str(format(self.llx, ".4f"))
                + " "
                + str(format(self.ury, ".4f"))
                + " "
                + str(format(self.urx, ".4f"))
                + " "
                + str(format(self.lly, ".4f"))
                + " ;\n"
            )

        m0_metal_str = ""  # hold the string of M0 metal pins
        # print the attached via pins as well
        if self.attached_pin != {}:
            for layer, metal_pin_list in self.attached_pin.items():
                # if layer name starts with V, then it is a via, ignore it
                if layer.startswith("V"):
                    continue
                f.write("      LAYER " + layer + " ;\n")
                for via_pin in metal_pin_list:
                    f.write(
                        "        RECT "
                        + str(format(via_pin.llx, ".4f"))
                        + " "
                        + str(format(via_pin.ury, ".4f"))
                        + " "
                        + str(format(via_pin.urx, ".4f"))
                        + " "
                        + str(format(via_pin.lly, ".4f"))
                        + " ;\n"
                    )
                # if layer is M1, then go through its M0 metals inside its attached_pin dict
                # if layer.startswith("M1"):
                #     for m1_metal in metal_pin_list:
                #         print(m1_metal.attached_pin)
                #         # if M0 is a key in the attached_pin dict
                #         if "M0" in m1_metal.attached_pin.keys():
                #             for m0_metal in m1_metal.attached_pin["M0"]:
                #                 m0_metal_str += (
                #                     "        RECT "
                #                     + str(format(m0_metal.llx, ".4f"))
                #                     + " "
                #                     + str(format(m0_metal.ury, ".4f"))
                #                     + " "
                #                     + str(format(m0_metal.urx, ".4f"))
                #                     + " "
                #                     + str(format(m0_metal.lly, ".4f"))
                #                     + " ;\n"
                #                 )
            # print M0 metals
            if m0_metal_str != "":
                f.write("      LAYER M0 ;\n")
                f.write(m0_metal_str)

        f.write("    END\n")
        f.write("  END " + self.pin_name + "\n")

    def print_LEF(self):
        print("PIN " + self.pin_name)
        print("  DIRECTION OUTPUT ;")
        print("  USE SIGNAL ;")
        print("  PORT")
        print("    LAYER " + self.layer + " ;")
        print(
            "      RECT "
            + str(format(self.llx, ".4f"))
            + " "
            + str(format(self.ury, ".4f"))
            + " "
            + str(format(self.urx, ".4f"))
            + " "
            + str(format(self.lly, ".4f"))
            + " ;\n"
        )
        print("  END")
        print("END " + self.pin_name)


class Obs:
    class coord_info:
        def __init__(self, *args, **kwargs):
            self.llx = kwargs.get("llx", 0.0)
            self.lly = kwargs.get("lly", 0.0)
            self.urx = kwargs.get("urx", 0.0)
            self.ury = kwargs.get("ury", 0.0)
            self.sort()

        def sort(self):
            if self.llx > self.urx:
                self.llx, self.urx = self.urx, self.llx
            if self.lly > self.ury:
                self.lly, self.ury = self.ury, self.lly

        # build hash function
        def __hash__(self):
            return hash((self.llx, self.lly, self.urx, self.ury))

    def __init__(self, *args, **kwargs):
        # [coord] => [layer]
        self.coord_dict = kwargs.get("coord_dict", None)
        if self.coord_dict is None:
            self.coord_dict = {}

    def set_coord_dict(self, coord_dict):
        self.coord_dict = coord_dict

    def add_coord(self, coord, layer):
        self.coord_dict[
            Obs.coord_info(llx=coord[0], lly=coord[1], urx=coord[2], ury=coord[3])
        ] = layer

    def write_LEF(self, f):
        if self.coord_dict == {}:
            return
        f.write("  OBS" + "\n")
        for layer_group in set(self.coord_dict.values()):
            f.write("      LAYER " + layer_group + " ;\n")
            for coord, layer in self.coord_dict.items():
                if layer == layer_group:
                    if layer == "M1":
                        f.write(
                            "        RECT "
                            + str(format(coord.llx, ".4f"))
                            + " "
                            + str(format(coord.ury, ".4f"))
                            + " "
                            + str(format(coord.urx, ".4f"))
                            + " "
                            + str(format(coord.lly, ".4f"))
                            + " ;\n"
                        )
                    else:
                        f.write(
                            "        RECT "
                            + str(format(coord.llx, ".4f"))
                            + " "
                            + str(format(coord.lly, ".4f"))
                            + " "
                            + str(format(coord.urx, ".4f"))
                            + " "
                            + str(format(coord.ury, ".4f"))
                            + " ;\n"
                        )
        f.write("  END" + "\n")

    def print_LEF(self):
        if self.coord_dict == {}:
            return
        print("OBS" + "\n")
        for layer_group in set(self.coord_dict.values()):
            print("  LAYER " + layer_group + " ;\n")
            for coord, layer in self.coord_dict.items():
                if layer == layer_group:
                    print(
                        "    RECT "
                        + str(format(coord[0], ".4f"))
                        + " "
                        + str(format(coord[1], ".4f"))
                        + " "
                        + str(format(coord[2], ".4f"))
                        + " "
                        + str(format(coord[3], ".4f"))
                        + " ;\n"
                    )
        print("END" + "\n")


def main(argv, argc):
    # check if enough arguments are provided
    if argc < 3:
        print("Usage: python3 genLef.py <input_gdt> <output_lef>")
        return
    input_gdt = argv[1]
    output_lef = argv[2]
    cppWidth = 0.0450
    cppHeight = 0.0  # subject to change

    # open and read the gdt file line by line
    with open(input_gdt) as f:
        lines = f.readlines()

    # remove whitespace characters like `\n` at the end of each line
    lines = [x.strip() for x in lines]

    read_mode = False
    cell_list = []
    m0_pin_list = []
    m1_pin_list = []
    V0_pin_list = []
    V1_pin_list = []
    tmp_pin_list = []
    tmp_pwr_pin_list = []
    tmp_cell_width = 0.0
    tmp_cell_height = 0.0

    for line in lines:
        # extract the cell name first
        if line.startswith("cell{c="):
            cell_name = line.split("'")[1]
            # print(cell_name)
            read_mode = True
            continue

        # extract the cell width and height
        if read_mode and line.startswith("b{100"):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # tmp_cell_width = float(floats[3])
            # tmp_cell_height = float(floats[-1])
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            tmp_cell_width = tmp_pt.get_ux() - tmp_pt.get_lx()
            tmp_cell_height = tmp_pt.get_uy() - tmp_pt.get_ly()
            cppHeight = tmp_cell_height
            # print(tmp_cell_width, tmp_cell_height)
            continue

        # extract the V0 vias/obs
        if read_mode and line.startswith("b{18"):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            # print("v0 -- lx: " + str(tmp_pt.get_lx()) + " ly: " + str(tmp_pt.get_ly()) + " ux: " + str(tmp_pt.get_ux()) + " uy: " + str(tmp_pt.get_uy()))
            # print("V0 -- lx: " + str(floats[1]) + " ly: " + str(floats[2]) + " ux: " + str(floats[3]) + " uy: " + str(floats[-1]))
            tmp_pin = Pin(
                llx=tmp_pt.get_lx(),
                lly=tmp_pt.get_ly(),
                urx=tmp_pt.get_ux(),
                ury=tmp_pt.get_uy(),
                layer="V0",
            )
            # tmp_pin_list.append(tmp_pin)
            V0_pin_list.append(tmp_pin)
            continue

        # extract the m0 pins/obs (except VDD/VSS)
        if (
            read_mode
            and line.startswith("b{15")
            and not line.startswith("b{15 xy(0.0000")
        ):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            # print("m0 -- lx: " + str(tmp_pt.get_lx()) + " ly: " + str(tmp_pt.get_ly()) + " ux: " + str(tmp_pt.get_ux()) + " uy: " + str(tmp_pt.get_uy()))
            # print("M0 -- lx: " + str(floats[1]) + " ly: " + str(floats[2]) + " ux: " + str(floats[3]) + " uy: " + str(floats[-1]))
            tmp_pin = Pin(
                llx=tmp_pt.get_lx(),
                lly=tmp_pt.get_ly(),
                urx=tmp_pt.get_ux(),
                ury=tmp_pt.get_uy(),
                layer="M0",
            )
            # tmp_pin_list.append(tmp_pin)
            m0_pin_list.append(tmp_pin)
            continue

        # extract the m1 pins/obs
        if read_mode and line.startswith("b{19"):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            # print("m1 -- lx: " + str(tmp_pt.get_lx()) + " ly: " + str(tmp_pt.get_ly()) + " ux: " + str(tmp_pt.get_ux()) + " uy: " + str(tmp_pt.get_uy()))
            # print("M1 -- lx: " + str(floats[1]) + " ly: " + str(floats[-1]) + " ux: " + str(floats[3]) + " uy: " + str(floats[2]))
            tmp_pin = Pin(
                llx=tmp_pt.get_lx(),
                lly=tmp_pt.get_ly(),
                urx=tmp_pt.get_ux(),
                ury=tmp_pt.get_uy(),
                layer="M1",
            )
            tmp_pin_list.append(tmp_pin)
            m1_pin_list.append(tmp_pin)
            continue

        if read_mode and line.startswith("t{19"):
            # extract all the floats with regex
            # floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            pattern = r'xy\(([^)]+)\)'
            match = re.search(pattern, line)
            floats = match.group(1).split() if match else []
            # extract the string within the single quote
            pin_name = line.split("'")[1]
            # print(pin_name)
            # print(floats)
            for pin in tmp_pin_list:
                if (
                    pin.if_pin_within_bbox(float(floats[0]), float(floats[1]))
                    and pin.layer == "M1"
                ):
                    # print("setting m1 pin name", pin_name, float(floats[0]), float(floats[1]))
                    pin.set_pin_name(pin_name)
                    break

        # extract the m2 pins/obs
        if read_mode and line.startswith("b{20"):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            # print("m2 -- lx: " + str(tmp_pt.get_lx()) + " ly: " + str(tmp_pt.get_ly()) + " ux: " + str(tmp_pt.get_ux()) + " uy: " + str(tmp_pt.get_uy()))
            # print("M2 -- lx: " + str(floats[1]) + " ly: " + str(floats[2]) + " ux: " + str(floats[3]) + " uy: " + str(floats[-1]))
            tmp_pin = Pin(
                llx=tmp_pt.get_lx(),
                lly=tmp_pt.get_ly(),
                urx=tmp_pt.get_ux(),
                ury=tmp_pt.get_uy(),
                layer="M2",
            )
            tmp_pin_list.append(tmp_pin)
            continue

        if read_mode and line.startswith("t{20"):
            # extract all the floats with regex
            # floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            pattern = r'xy\(([^)]+)\)'
            match = re.search(pattern, line)
            floats = match.group(1).split() if match else []
            # extract the string within the single quote
            pin_name = line.split("'")[1]
            for pin in tmp_pin_list:
                if (
                    pin.if_pin_within_bbox(float(floats[0]), float(floats[1]))
                    and pin.layer == "M2"
                ):
                    pin.set_pin_name(pin_name)
                    break

        # extract the V1 vias/obs
        if read_mode and line.startswith("b{21"):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            # print("v1 -- lx: " + str(tmp_pt.get_lx()) + " ly: " + str(tmp_pt.get_ly()) + " ux: " + str(tmp_pt.get_ux()) + " uy: " + str(tmp_pt.get_uy()))
            # print("V1 -- lx: " + str(floats[1]) + " ly: " + str(floats[2]) + " ux: " + str(floats[3]) + " uy: " + str(floats[-1]))
            tmp_pin = Pin(
                llx=tmp_pt.get_lx(),
                lly=tmp_pt.get_ly(),
                urx=tmp_pt.get_ux(),
                ury=tmp_pt.get_uy(),
                layer="V1",
            )
            tmp_pin_list.append(tmp_pin)
            V1_pin_list.append(tmp_pin)
            continue

        # extract vdd/vss pins (M0)
        if read_mode and line.startswith("b{15 xy(0.0000"):
            # extract all the floats with regex
            floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            # convert every element to a float
            floats = [float(x) for x in floats]
            tmp_pt = Point(floats[1:])
            tmp_pin = Pin(
                llx=tmp_pt.get_lx(),
                lly=tmp_pt.get_ly(),
                urx=tmp_pt.get_ux(),
                ury=tmp_pt.get_uy(),
                layer="M0",
            )
            # print(tmp_pin.llx, tmp_pin.lly, tmp_pin.urx, tmp_pin.ury)
            # tmp_pwr_pin_list.append(tmp_pin)
            tmp_pin_list.append(tmp_pin)
            continue

        if read_mode and line.startswith("t{15"):
            # extract all the floats with regex
            # floats = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            pattern = r'xy\(([^)]+)\)'
            match = re.search(pattern, line)
            floats = match.group(1).split() if match else []
            # find the digits within xy(###, ####)
            # print(floats)
            # extract the string within the single quote
            pin_name = line.split("'")[1]
            # print(pin_name)
            for pin in m0_pin_list:
                if pin.if_pin_within_bbox(float(floats[0]), float(floats[1])):
                    pin.set_pin_name(pin_name)
                    if pin_name == "VDD" or pin_name == "VSS":
                        # TODO: temp fix
                        if pin.llx < 0.0:
                            offset_amount = 0.0 - pin.llx
                            pin.llx += offset_amount
                            pin.urx -= offset_amount
                            print("offset amount", offset_amount)
                        tmp_pwr_pin_list.append(pin)
                    else:
                        pin.set_pin_name(pin_name)
                        # print("setting m0 pin name", pin_name, float(floats[-2]), float(floats[-1]))
                else:
                    # print(f"     {float(floats[-2]), float(floats[-1])} not within bbox")
                    pass

        # end reading the cell
        if line.startswith("}"):
            read_mode = False
            # print("m0 length: " + str(len(m0_pin_list)) + " " + str(len([pin for pin in tmp_pin_list if pin.layer == "M0"])))
            # print("m1 length: " + str(len(m1_pin_list)) + " " + str(len([pin for pin in tmp_pin_list if pin.layer == "M1"])))
            # print("m2 length: " + str(len([pin for pin in tmp_pin_list if pin.layer == "M2"])))
            # print("v0 length: " + str(len(V0_pin_list)) + " " + str(len([pin for pin in tmp_pin_list if pin.layer == "V0"])))
            # print("v1 length: " + str(len(V1_pin_list)) + " " + str(len([pin for pin in tmp_pin_list if pin.layer == "V1"])))

            # go through the pin list and print the pins
            # print("FLAG 1")
            # for pin in tmp_pin_list:
            #     print("     ", pin.pin_name, pin.layer, pin.llx, pin.lly, pin.urx, pin.ury)

            # add M0 pins to the tmp_pin_list
            for m0_pin in m0_pin_list:
                if m0_pin.pin_name != None:
                    tmp_pin_list.append(m0_pin)

            # match M1 pins with V0 vias (if any), add the V0 via to the attached_pin dict
            for pin in tmp_pin_list:
                if pin.layer == "M1":
                    for via_pin in V0_pin_list:
                        if pin.if_via_within_bbox(via_pin):
                            # print("M1 connected to V0")
                            pass
            
            # print("FLAG 2")
            # for pin in tmp_pin_list:
            #     print("     ", pin.pin_name, pin.layer, pin.llx, pin.lly, pin.urx, pin.ury)

            # match M0 pins with M1 pins (if any)
            for m0_pin in m0_pin_list:
                for m1_pin in tmp_pin_list:
                    if m0_pin.layer == "M0" and m1_pin.layer == "M1":
                        if m1_pin.if_metal_pin_connected_to_via(m0_pin):
                            pass

            # match M2 pins with V1 vias (if any)
            for pin in tmp_pin_list:
                if pin.layer == "M2":
                    for via_pin in V1_pin_list:
                        if pin.if_via_within_bbox(via_pin):
                            pass
            
            # print("FLAG 3")
            # for pin in tmp_pin_list:
            #     print("     ", pin.pin_name, pin.layer, pin.llx, pin.lly, pin.urx, pin.ury)

            # print("m1_pin_list", [pin.pin_name for pin in m1_pin_list])

            # match M1 pins with M2 pins (if any)
            for m1_pin in m1_pin_list:
                # skip if the pin is already set
                if m1_pin.pin_name in Pin.signal_direction_dict.keys():
                    continue
                for m2_pin in tmp_pin_list:
                    if m1_pin.layer == "M1" and m2_pin.layer == "M2":
                        if m2_pin.if_metal_pin_connected_to_via(m1_pin):
                            # print(m2_pin.pin_name, m1_pin.pin_name, "M1 connected to M2")
                            pass
                        else:
                            # print(m2_pin.pin_name, m1_pin.pin_name, "M1 not connected to M2")
                            pass
            
            # print("last before obs", [pin.pin_name for pin in tmp_pin_list])
            # if a pin has no name, then it is an obs
            tmp_obs = Obs()
            tmp_pin_list_copy = (
                tmp_pin_list.copy()
            )  # prevent the list from being modified during the iteration
            for pin in tmp_pin_list:
                if pin.pin_name == None:
                    tmp_obs.add_coord((pin.llx, pin.ury, pin.urx, pin.lly), pin.layer)
                    # print("obs found due to no pin name, layer: " + pin.layer)
                    # remove the obs from the pin list
                    tmp_pin_list_copy.remove(pin)
                # remove the pwr pins from the pin list
                if pin.pin_name == "VDD" or pin.pin_name == "VSS":
                    # print("pwr pin found, layer: " + pin.layer)
                    tmp_pin_list_copy.remove(pin)
            for m0_pin in m0_pin_list:
                if m0_pin.pin_name == None or m0_pin.pin_name.startswith("unknown"):
                    # print("obs found due to unknown, layer: " + m0_pin.layer)
                    tmp_obs.add_coord(
                        (m0_pin.llx, m0_pin.lly, m0_pin.urx, m0_pin.ury), m0_pin.layer
                    )
                    # print("obs found, layer: " + m0_pin.layer)
                    # remove the obs from the pin list
            # update the pin list
            tmp_pin_list = tmp_pin_list_copy.copy()

            # put V0 vias as obs
            for via_pin in V0_pin_list:
                tmp_obs.add_coord(
                    (via_pin.llx, via_pin.ury, via_pin.urx, via_pin.lly), via_pin.layer
                )
            
            # print(tmp_pin_list)

            tmp_cell = Cell(
                cell_name=cell_name,
                pin_list=tmp_pin_list,
                obs_list=tmp_obs,
                pwr_pin_list=tmp_pwr_pin_list,
            )
            tmp_cell.set_cell_width(tmp_cell_width)
            tmp_cell.set_cell_height(tmp_cell_height)
            cell_list.append(tmp_cell)

            # empty the tmp_pin_list
            m0_pin_list = []
            m1_pin_list = []
            V0_pin_list = []
            V1_pin_list = []
            tmp_pin_list = []
            tmp_pwr_pin_list = []
            continue

    # cppWidth = 0.0450
    # cppHeight = 0.1680

    # TODO: idk why i need this, but this fix the bug so let it be :)
    # remove any cell with duplicate names, (keep the first one)
    visited_cell_names = set()
    cell_list_copy = []
    for cell in cell_list:
        if cell.cell_name not in visited_cell_names:
            visited_cell_names.add(cell.cell_name)
            cell_list_copy.append(cell)
    cell_list = cell_list_copy
        

    with open(output_lef, "w") as f:
        f.write("VERSION 5.8 ;\n")
        f.write('BUSBITCHARS "[]" ;\n')
        f.write('DIVIDERCHAR "/" ;\n')
        f.write("CLEARANCEMEASURE EUCLIDEAN ;\n")
        f.write("\n")
        f.write("SITE coresite\n")
        f.write(
            "    SIZE "
            + str(format(cppWidth, ".4f"))
            + " BY "
            + str(format(cppHeight, ".4f"))
            + " ;\n"
        )
        f.write("    CLASS CORE ;\n")
        f.write("    SYMMETRY X Y ;\n")
        f.write("END coresite\n")
        f.write("\n")
        for cell in cell_list:
            cell.write_LEF(f)
            f.write("\n")


if __name__ == "__main__":
    main(sys.argv, len(sys.argv))