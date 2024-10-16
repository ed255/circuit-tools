/* Generated by Yosys 0.45+11 (git sha1 e8951aba29faf774e475f20c1405162993235d7f, g++ 14.2.1 -O2 -fexceptions -fstack-protector-strong -m64 -march=x86-64 -mtune=generic -fasynchronous-unwind-tables -fstack-clash-protection -fcf-protection -fno-omit-frame-pointer -mno-omit-leaf-frame-pointer -fPIC -O3) */

(* top =  1  *)
(* src = "/tmp/input.v:1.1-19.10" *)
module entrypoint(a0, b0, _out0_0);
  wire _00_;
  wire _01_;
  wire _02_;
  wire _03_;
  wire _04_;
  wire _05_;
  wire _06_;
  wire _07_;
  wire _08_;
  wire _09_;
  wire _10_;
  wire _11_;
  wire _12_;
  wire _13_;
  wire _14_;
  wire _15_;
  wire _16_;
  wire _17_;
  wire _18_;
  wire _19_;
  wire _20_;
  wire _21_;
  wire _22_;
  wire _23_;
  wire _24_;
  wire _25_;
  (* src = "/tmp/input.v:4.21-4.28" *)
  output [7:0] _out0_0;
  wire [7:0] _out0_0;
  (* src = "/tmp/input.v:2.20-2.22" *)
  input [7:0] a0;
  wire [7:0] a0;
  (* src = "/tmp/input.v:3.20-3.22" *)
  input [7:0] b0;
  wire [7:0] b0;
  AND _26_ (
    .A(b0[0]),
    .B(a0[0]),
    .Y(_00_)
  );
  NAND _27_ (
    .A(b0[1]),
    .B(a0[1]),
    .Y(_01_)
  );
  XOR _28_ (
    .A(b0[1]),
    .B(a0[1]),
    .Y(_02_)
  );
  NAND _29_ (
    .A(_00_),
    .B(_02_),
    .Y(_03_)
  );
  XOR _30_ (
    .A(_00_),
    .B(_02_),
    .Y(_out0_0[1])
  );
  NAND _31_ (
    .A(_01_),
    .B(_03_),
    .Y(_04_)
  );
  NAND _32_ (
    .A(b0[2]),
    .B(a0[2]),
    .Y(_05_)
  );
  XOR _33_ (
    .A(b0[2]),
    .B(a0[2]),
    .Y(_06_)
  );
  NAND _34_ (
    .A(_04_),
    .B(_06_),
    .Y(_07_)
  );
  XOR _35_ (
    .A(_04_),
    .B(_06_),
    .Y(_out0_0[2])
  );
  NAND _36_ (
    .A(_05_),
    .B(_07_),
    .Y(_08_)
  );
  NAND _37_ (
    .A(b0[3]),
    .B(a0[3]),
    .Y(_09_)
  );
  XOR _38_ (
    .A(b0[3]),
    .B(a0[3]),
    .Y(_10_)
  );
  NAND _39_ (
    .A(_08_),
    .B(_10_),
    .Y(_11_)
  );
  XOR _40_ (
    .A(_08_),
    .B(_10_),
    .Y(_out0_0[3])
  );
  NAND _41_ (
    .A(_09_),
    .B(_11_),
    .Y(_12_)
  );
  NAND _42_ (
    .A(b0[4]),
    .B(a0[4]),
    .Y(_13_)
  );
  XOR _43_ (
    .A(b0[4]),
    .B(a0[4]),
    .Y(_14_)
  );
  NAND _44_ (
    .A(_12_),
    .B(_14_),
    .Y(_15_)
  );
  XOR _45_ (
    .A(_12_),
    .B(_14_),
    .Y(_out0_0[4])
  );
  NAND _46_ (
    .A(_13_),
    .B(_15_),
    .Y(_16_)
  );
  NAND _47_ (
    .A(b0[5]),
    .B(a0[5]),
    .Y(_17_)
  );
  XOR _48_ (
    .A(b0[5]),
    .B(a0[5]),
    .Y(_18_)
  );
  NAND _49_ (
    .A(_16_),
    .B(_18_),
    .Y(_19_)
  );
  XOR _50_ (
    .A(_16_),
    .B(_18_),
    .Y(_out0_0[5])
  );
  NAND _51_ (
    .A(_17_),
    .B(_19_),
    .Y(_20_)
  );
  NAND _52_ (
    .A(b0[6]),
    .B(a0[6]),
    .Y(_21_)
  );
  XOR _53_ (
    .A(b0[6]),
    .B(a0[6]),
    .Y(_22_)
  );
  NAND _54_ (
    .A(_20_),
    .B(_22_),
    .Y(_23_)
  );
  XOR _55_ (
    .A(_20_),
    .B(_22_),
    .Y(_out0_0[6])
  );
  NAND _56_ (
    .A(_21_),
    .B(_23_),
    .Y(_24_)
  );
  XNOR _57_ (
    .A(b0[7]),
    .B(a0[7]),
    .Y(_25_)
  );
  XNOR _58_ (
    .A(_24_),
    .B(_25_),
    .Y(_out0_0[7])
  );
  XOR _59_ (
    .A(b0[0]),
    .B(a0[0]),
    .Y(_out0_0[0])
  );
endmodule
