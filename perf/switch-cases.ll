; PERF: switch dispatch vs. case count.
; A loop switching on i mod 256 over 256 cases. denote_terminator
; re-elaborates every case literal (coerce_integer_to_int via
; map_monad) on each execution before the linear select_switch scan,
; so a switch hit costs ~2 us per case: this test spends most of its
; time re-processing constants. Pre-elaborating the cases (they are
; syntactically constant) would make this test collapse toward
; loop-phi-arith.ll's per-iteration cost.
;
; Tune: regenerate with a different C / K (see perf/README.md).
; Result is sum of (i mod C) for i in [0,K) = K*(C-1)/2.

define i64 @main(i64 %argc, i8** %argv) {
entry:
  br label %header
header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %latch ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %latch ]
  %c = icmp eq i64 %i, 8192
  br i1 %c, label %exit, label %sw
sw:
  %m = urem i64 %i, 256
  switch i64 %m, label %case0 [ i64 0, label %case0 i64 1, label %case1 i64 2, label %case2 i64 3, label %case3 i64 4, label %case4 i64 5, label %case5 i64 6, label %case6 i64 7, label %case7 i64 8, label %case8 i64 9, label %case9 i64 10, label %case10 i64 11, label %case11 i64 12, label %case12 i64 13, label %case13 i64 14, label %case14 i64 15, label %case15 i64 16, label %case16 i64 17, label %case17 i64 18, label %case18 i64 19, label %case19 i64 20, label %case20 i64 21, label %case21 i64 22, label %case22 i64 23, label %case23 i64 24, label %case24 i64 25, label %case25 i64 26, label %case26 i64 27, label %case27 i64 28, label %case28 i64 29, label %case29 i64 30, label %case30 i64 31, label %case31 i64 32, label %case32 i64 33, label %case33 i64 34, label %case34 i64 35, label %case35 i64 36, label %case36 i64 37, label %case37 i64 38, label %case38 i64 39, label %case39 i64 40, label %case40 i64 41, label %case41 i64 42, label %case42 i64 43, label %case43 i64 44, label %case44 i64 45, label %case45 i64 46, label %case46 i64 47, label %case47 i64 48, label %case48 i64 49, label %case49 i64 50, label %case50 i64 51, label %case51 i64 52, label %case52 i64 53, label %case53 i64 54, label %case54 i64 55, label %case55 i64 56, label %case56 i64 57, label %case57 i64 58, label %case58 i64 59, label %case59 i64 60, label %case60 i64 61, label %case61 i64 62, label %case62 i64 63, label %case63 i64 64, label %case64 i64 65, label %case65 i64 66, label %case66 i64 67, label %case67 i64 68, label %case68 i64 69, label %case69 i64 70, label %case70 i64 71, label %case71 i64 72, label %case72 i64 73, label %case73 i64 74, label %case74 i64 75, label %case75 i64 76, label %case76 i64 77, label %case77 i64 78, label %case78 i64 79, label %case79 i64 80, label %case80 i64 81, label %case81 i64 82, label %case82 i64 83, label %case83 i64 84, label %case84 i64 85, label %case85 i64 86, label %case86 i64 87, label %case87 i64 88, label %case88 i64 89, label %case89 i64 90, label %case90 i64 91, label %case91 i64 92, label %case92 i64 93, label %case93 i64 94, label %case94 i64 95, label %case95 i64 96, label %case96 i64 97, label %case97 i64 98, label %case98 i64 99, label %case99 i64 100, label %case100 i64 101, label %case101 i64 102, label %case102 i64 103, label %case103 i64 104, label %case104 i64 105, label %case105 i64 106, label %case106 i64 107, label %case107 i64 108, label %case108 i64 109, label %case109 i64 110, label %case110 i64 111, label %case111 i64 112, label %case112 i64 113, label %case113 i64 114, label %case114 i64 115, label %case115 i64 116, label %case116 i64 117, label %case117 i64 118, label %case118 i64 119, label %case119 i64 120, label %case120 i64 121, label %case121 i64 122, label %case122 i64 123, label %case123 i64 124, label %case124 i64 125, label %case125 i64 126, label %case126 i64 127, label %case127 i64 128, label %case128 i64 129, label %case129 i64 130, label %case130 i64 131, label %case131 i64 132, label %case132 i64 133, label %case133 i64 134, label %case134 i64 135, label %case135 i64 136, label %case136 i64 137, label %case137 i64 138, label %case138 i64 139, label %case139 i64 140, label %case140 i64 141, label %case141 i64 142, label %case142 i64 143, label %case143 i64 144, label %case144 i64 145, label %case145 i64 146, label %case146 i64 147, label %case147 i64 148, label %case148 i64 149, label %case149 i64 150, label %case150 i64 151, label %case151 i64 152, label %case152 i64 153, label %case153 i64 154, label %case154 i64 155, label %case155 i64 156, label %case156 i64 157, label %case157 i64 158, label %case158 i64 159, label %case159 i64 160, label %case160 i64 161, label %case161 i64 162, label %case162 i64 163, label %case163 i64 164, label %case164 i64 165, label %case165 i64 166, label %case166 i64 167, label %case167 i64 168, label %case168 i64 169, label %case169 i64 170, label %case170 i64 171, label %case171 i64 172, label %case172 i64 173, label %case173 i64 174, label %case174 i64 175, label %case175 i64 176, label %case176 i64 177, label %case177 i64 178, label %case178 i64 179, label %case179 i64 180, label %case180 i64 181, label %case181 i64 182, label %case182 i64 183, label %case183 i64 184, label %case184 i64 185, label %case185 i64 186, label %case186 i64 187, label %case187 i64 188, label %case188 i64 189, label %case189 i64 190, label %case190 i64 191, label %case191 i64 192, label %case192 i64 193, label %case193 i64 194, label %case194 i64 195, label %case195 i64 196, label %case196 i64 197, label %case197 i64 198, label %case198 i64 199, label %case199 i64 200, label %case200 i64 201, label %case201 i64 202, label %case202 i64 203, label %case203 i64 204, label %case204 i64 205, label %case205 i64 206, label %case206 i64 207, label %case207 i64 208, label %case208 i64 209, label %case209 i64 210, label %case210 i64 211, label %case211 i64 212, label %case212 i64 213, label %case213 i64 214, label %case214 i64 215, label %case215 i64 216, label %case216 i64 217, label %case217 i64 218, label %case218 i64 219, label %case219 i64 220, label %case220 i64 221, label %case221 i64 222, label %case222 i64 223, label %case223 i64 224, label %case224 i64 225, label %case225 i64 226, label %case226 i64 227, label %case227 i64 228, label %case228 i64 229, label %case229 i64 230, label %case230 i64 231, label %case231 i64 232, label %case232 i64 233, label %case233 i64 234, label %case234 i64 235, label %case235 i64 236, label %case236 i64 237, label %case237 i64 238, label %case238 i64 239, label %case239 i64 240, label %case240 i64 241, label %case241 i64 242, label %case242 i64 243, label %case243 i64 244, label %case244 i64 245, label %case245 i64 246, label %case246 i64 247, label %case247 i64 248, label %case248 i64 249, label %case249 i64 250, label %case250 i64 251, label %case251 i64 252, label %case252 i64 253, label %case253 i64 254, label %case254 i64 255, label %case255 ]
case0:
  br label %join
case1:
  br label %join
case2:
  br label %join
case3:
  br label %join
case4:
  br label %join
case5:
  br label %join
case6:
  br label %join
case7:
  br label %join
case8:
  br label %join
case9:
  br label %join
case10:
  br label %join
case11:
  br label %join
case12:
  br label %join
case13:
  br label %join
case14:
  br label %join
case15:
  br label %join
case16:
  br label %join
case17:
  br label %join
case18:
  br label %join
case19:
  br label %join
case20:
  br label %join
case21:
  br label %join
case22:
  br label %join
case23:
  br label %join
case24:
  br label %join
case25:
  br label %join
case26:
  br label %join
case27:
  br label %join
case28:
  br label %join
case29:
  br label %join
case30:
  br label %join
case31:
  br label %join
case32:
  br label %join
case33:
  br label %join
case34:
  br label %join
case35:
  br label %join
case36:
  br label %join
case37:
  br label %join
case38:
  br label %join
case39:
  br label %join
case40:
  br label %join
case41:
  br label %join
case42:
  br label %join
case43:
  br label %join
case44:
  br label %join
case45:
  br label %join
case46:
  br label %join
case47:
  br label %join
case48:
  br label %join
case49:
  br label %join
case50:
  br label %join
case51:
  br label %join
case52:
  br label %join
case53:
  br label %join
case54:
  br label %join
case55:
  br label %join
case56:
  br label %join
case57:
  br label %join
case58:
  br label %join
case59:
  br label %join
case60:
  br label %join
case61:
  br label %join
case62:
  br label %join
case63:
  br label %join
case64:
  br label %join
case65:
  br label %join
case66:
  br label %join
case67:
  br label %join
case68:
  br label %join
case69:
  br label %join
case70:
  br label %join
case71:
  br label %join
case72:
  br label %join
case73:
  br label %join
case74:
  br label %join
case75:
  br label %join
case76:
  br label %join
case77:
  br label %join
case78:
  br label %join
case79:
  br label %join
case80:
  br label %join
case81:
  br label %join
case82:
  br label %join
case83:
  br label %join
case84:
  br label %join
case85:
  br label %join
case86:
  br label %join
case87:
  br label %join
case88:
  br label %join
case89:
  br label %join
case90:
  br label %join
case91:
  br label %join
case92:
  br label %join
case93:
  br label %join
case94:
  br label %join
case95:
  br label %join
case96:
  br label %join
case97:
  br label %join
case98:
  br label %join
case99:
  br label %join
case100:
  br label %join
case101:
  br label %join
case102:
  br label %join
case103:
  br label %join
case104:
  br label %join
case105:
  br label %join
case106:
  br label %join
case107:
  br label %join
case108:
  br label %join
case109:
  br label %join
case110:
  br label %join
case111:
  br label %join
case112:
  br label %join
case113:
  br label %join
case114:
  br label %join
case115:
  br label %join
case116:
  br label %join
case117:
  br label %join
case118:
  br label %join
case119:
  br label %join
case120:
  br label %join
case121:
  br label %join
case122:
  br label %join
case123:
  br label %join
case124:
  br label %join
case125:
  br label %join
case126:
  br label %join
case127:
  br label %join
case128:
  br label %join
case129:
  br label %join
case130:
  br label %join
case131:
  br label %join
case132:
  br label %join
case133:
  br label %join
case134:
  br label %join
case135:
  br label %join
case136:
  br label %join
case137:
  br label %join
case138:
  br label %join
case139:
  br label %join
case140:
  br label %join
case141:
  br label %join
case142:
  br label %join
case143:
  br label %join
case144:
  br label %join
case145:
  br label %join
case146:
  br label %join
case147:
  br label %join
case148:
  br label %join
case149:
  br label %join
case150:
  br label %join
case151:
  br label %join
case152:
  br label %join
case153:
  br label %join
case154:
  br label %join
case155:
  br label %join
case156:
  br label %join
case157:
  br label %join
case158:
  br label %join
case159:
  br label %join
case160:
  br label %join
case161:
  br label %join
case162:
  br label %join
case163:
  br label %join
case164:
  br label %join
case165:
  br label %join
case166:
  br label %join
case167:
  br label %join
case168:
  br label %join
case169:
  br label %join
case170:
  br label %join
case171:
  br label %join
case172:
  br label %join
case173:
  br label %join
case174:
  br label %join
case175:
  br label %join
case176:
  br label %join
case177:
  br label %join
case178:
  br label %join
case179:
  br label %join
case180:
  br label %join
case181:
  br label %join
case182:
  br label %join
case183:
  br label %join
case184:
  br label %join
case185:
  br label %join
case186:
  br label %join
case187:
  br label %join
case188:
  br label %join
case189:
  br label %join
case190:
  br label %join
case191:
  br label %join
case192:
  br label %join
case193:
  br label %join
case194:
  br label %join
case195:
  br label %join
case196:
  br label %join
case197:
  br label %join
case198:
  br label %join
case199:
  br label %join
case200:
  br label %join
case201:
  br label %join
case202:
  br label %join
case203:
  br label %join
case204:
  br label %join
case205:
  br label %join
case206:
  br label %join
case207:
  br label %join
case208:
  br label %join
case209:
  br label %join
case210:
  br label %join
case211:
  br label %join
case212:
  br label %join
case213:
  br label %join
case214:
  br label %join
case215:
  br label %join
case216:
  br label %join
case217:
  br label %join
case218:
  br label %join
case219:
  br label %join
case220:
  br label %join
case221:
  br label %join
case222:
  br label %join
case223:
  br label %join
case224:
  br label %join
case225:
  br label %join
case226:
  br label %join
case227:
  br label %join
case228:
  br label %join
case229:
  br label %join
case230:
  br label %join
case231:
  br label %join
case232:
  br label %join
case233:
  br label %join
case234:
  br label %join
case235:
  br label %join
case236:
  br label %join
case237:
  br label %join
case238:
  br label %join
case239:
  br label %join
case240:
  br label %join
case241:
  br label %join
case242:
  br label %join
case243:
  br label %join
case244:
  br label %join
case245:
  br label %join
case246:
  br label %join
case247:
  br label %join
case248:
  br label %join
case249:
  br label %join
case250:
  br label %join
case251:
  br label %join
case252:
  br label %join
case253:
  br label %join
case254:
  br label %join
case255:
  br label %join
join:
  br label %latch
latch:
  %acc.next = add i64 %acc, %m
  %i.next = add i64 %i, 1
  br label %header
exit:
  ret i64 %acc
}

; ASSERT EQ: i64 1044480 = call i64 @main(i64 0, i8** null)
