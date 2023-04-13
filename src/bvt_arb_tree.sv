// Copyright 2023 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
//
// Based on the work of Mikhail Khalilov <mikhail.khalilov@inf.ethz.ch>
//

/// Hardware-friendly implementation of the borrowed virtual time (BVT) scheduling method
/// [C++ Implementation](https://github.com/miharulidze/pspin/blob/osmosis_fmqs/hw/verilator_model/src/FMQEngine.hpp#L407)
/// [BVT Paper](https://rcs.uwaterloo.ca/papers/bvt.pdf)
module bvt_arb_tree #(
  /// Number of inputs to be arbitrated.
  parameter int unsigned NumIn      = 32'd64,
  /// Data type of the payload
  parameter type         data_t     = logic,
  /// The width of the virtual time elements
  parameter int unsigned TimeWidth  = 32'd64,
  /// The width of the priority
  parameter int unsigned PrioWidth  = 32'd8,
  /// Dependent parameter, do **not** overwrite.
  /// Type for the priority
  parameter type         priority_t = logic [PrioWidth-1:0]
  /// Dependent parameter, do **not** overwrite.
  /// Width of the arbitration priority signal and the arbitrated index.
  parameter int unsigned IdxWidth   = (NumIn > 32'd1) ? unsigned'($clog2(NumIn)) : 32'd1,
  /// Dependent parameter, do **not** overwrite.
  /// Type for defining the arbitration priority and arbitrated index signal.
  parameter type         idx_t      = logic [IdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
  input  logic                  clk_i,
  /// Asynchronous reset, active low.
  input  logic                  rst_ni,
  /// The priorities: larger value -> higher prio
  input  priority_t [NumIn-1:0] prio_i,
  /// Input requests arbitration.
  input  logic      [NumIn-1:0] req_i,
  /// Input request is granted.
  output logic      [NumIn-1:0] gnt_o,
  /// Input data for arbitration.
  input  data_t     [NumIn-1:0] data_i,
  /// Output request is valid.
  output logic                  req_o,
  /// Output request is granted.
  input  logic                  gnt_i,
  /// Output data.
  output data_t                 data_o,
  /// Index from which input the data came from.
  output idx_t                  idx_o
);

  /// type holding the virtual time of every input
  typedef logic [TimeWidth-1:0] time_t;

  time_t [NumIn-1:0] virtual_time_d, virual_time_q;



endmodule