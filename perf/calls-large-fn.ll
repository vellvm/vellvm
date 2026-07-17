; PERF: per-call denotation setup cost as a function of callee size.
; A trivial callee padded with 400 unreachable blocks, called 40000
; times from a counted loop. Any per-call work proportional to the
; callee's block count shows up here multiplied by the call count --
; e.g. building the block-id map per call instead of once per
; definition (in denote_function) made this test ~4x slower, and
; hundreds of times slower at larger D. Compare per-call cost against
; calls-fib.ll (many calls, minimal callee).
;
; Tune: regenerate with a different D / K (see perf/README.md).
; Result is K (the callee is the successor function).

define i64 @f(i64 %x) {
entry:
  %r = add i64 %x, 1
  ret i64 %r
dead0:
  ret i64 -1
dead1:
  ret i64 -1
dead2:
  ret i64 -1
dead3:
  ret i64 -1
dead4:
  ret i64 -1
dead5:
  ret i64 -1
dead6:
  ret i64 -1
dead7:
  ret i64 -1
dead8:
  ret i64 -1
dead9:
  ret i64 -1
dead10:
  ret i64 -1
dead11:
  ret i64 -1
dead12:
  ret i64 -1
dead13:
  ret i64 -1
dead14:
  ret i64 -1
dead15:
  ret i64 -1
dead16:
  ret i64 -1
dead17:
  ret i64 -1
dead18:
  ret i64 -1
dead19:
  ret i64 -1
dead20:
  ret i64 -1
dead21:
  ret i64 -1
dead22:
  ret i64 -1
dead23:
  ret i64 -1
dead24:
  ret i64 -1
dead25:
  ret i64 -1
dead26:
  ret i64 -1
dead27:
  ret i64 -1
dead28:
  ret i64 -1
dead29:
  ret i64 -1
dead30:
  ret i64 -1
dead31:
  ret i64 -1
dead32:
  ret i64 -1
dead33:
  ret i64 -1
dead34:
  ret i64 -1
dead35:
  ret i64 -1
dead36:
  ret i64 -1
dead37:
  ret i64 -1
dead38:
  ret i64 -1
dead39:
  ret i64 -1
dead40:
  ret i64 -1
dead41:
  ret i64 -1
dead42:
  ret i64 -1
dead43:
  ret i64 -1
dead44:
  ret i64 -1
dead45:
  ret i64 -1
dead46:
  ret i64 -1
dead47:
  ret i64 -1
dead48:
  ret i64 -1
dead49:
  ret i64 -1
dead50:
  ret i64 -1
dead51:
  ret i64 -1
dead52:
  ret i64 -1
dead53:
  ret i64 -1
dead54:
  ret i64 -1
dead55:
  ret i64 -1
dead56:
  ret i64 -1
dead57:
  ret i64 -1
dead58:
  ret i64 -1
dead59:
  ret i64 -1
dead60:
  ret i64 -1
dead61:
  ret i64 -1
dead62:
  ret i64 -1
dead63:
  ret i64 -1
dead64:
  ret i64 -1
dead65:
  ret i64 -1
dead66:
  ret i64 -1
dead67:
  ret i64 -1
dead68:
  ret i64 -1
dead69:
  ret i64 -1
dead70:
  ret i64 -1
dead71:
  ret i64 -1
dead72:
  ret i64 -1
dead73:
  ret i64 -1
dead74:
  ret i64 -1
dead75:
  ret i64 -1
dead76:
  ret i64 -1
dead77:
  ret i64 -1
dead78:
  ret i64 -1
dead79:
  ret i64 -1
dead80:
  ret i64 -1
dead81:
  ret i64 -1
dead82:
  ret i64 -1
dead83:
  ret i64 -1
dead84:
  ret i64 -1
dead85:
  ret i64 -1
dead86:
  ret i64 -1
dead87:
  ret i64 -1
dead88:
  ret i64 -1
dead89:
  ret i64 -1
dead90:
  ret i64 -1
dead91:
  ret i64 -1
dead92:
  ret i64 -1
dead93:
  ret i64 -1
dead94:
  ret i64 -1
dead95:
  ret i64 -1
dead96:
  ret i64 -1
dead97:
  ret i64 -1
dead98:
  ret i64 -1
dead99:
  ret i64 -1
dead100:
  ret i64 -1
dead101:
  ret i64 -1
dead102:
  ret i64 -1
dead103:
  ret i64 -1
dead104:
  ret i64 -1
dead105:
  ret i64 -1
dead106:
  ret i64 -1
dead107:
  ret i64 -1
dead108:
  ret i64 -1
dead109:
  ret i64 -1
dead110:
  ret i64 -1
dead111:
  ret i64 -1
dead112:
  ret i64 -1
dead113:
  ret i64 -1
dead114:
  ret i64 -1
dead115:
  ret i64 -1
dead116:
  ret i64 -1
dead117:
  ret i64 -1
dead118:
  ret i64 -1
dead119:
  ret i64 -1
dead120:
  ret i64 -1
dead121:
  ret i64 -1
dead122:
  ret i64 -1
dead123:
  ret i64 -1
dead124:
  ret i64 -1
dead125:
  ret i64 -1
dead126:
  ret i64 -1
dead127:
  ret i64 -1
dead128:
  ret i64 -1
dead129:
  ret i64 -1
dead130:
  ret i64 -1
dead131:
  ret i64 -1
dead132:
  ret i64 -1
dead133:
  ret i64 -1
dead134:
  ret i64 -1
dead135:
  ret i64 -1
dead136:
  ret i64 -1
dead137:
  ret i64 -1
dead138:
  ret i64 -1
dead139:
  ret i64 -1
dead140:
  ret i64 -1
dead141:
  ret i64 -1
dead142:
  ret i64 -1
dead143:
  ret i64 -1
dead144:
  ret i64 -1
dead145:
  ret i64 -1
dead146:
  ret i64 -1
dead147:
  ret i64 -1
dead148:
  ret i64 -1
dead149:
  ret i64 -1
dead150:
  ret i64 -1
dead151:
  ret i64 -1
dead152:
  ret i64 -1
dead153:
  ret i64 -1
dead154:
  ret i64 -1
dead155:
  ret i64 -1
dead156:
  ret i64 -1
dead157:
  ret i64 -1
dead158:
  ret i64 -1
dead159:
  ret i64 -1
dead160:
  ret i64 -1
dead161:
  ret i64 -1
dead162:
  ret i64 -1
dead163:
  ret i64 -1
dead164:
  ret i64 -1
dead165:
  ret i64 -1
dead166:
  ret i64 -1
dead167:
  ret i64 -1
dead168:
  ret i64 -1
dead169:
  ret i64 -1
dead170:
  ret i64 -1
dead171:
  ret i64 -1
dead172:
  ret i64 -1
dead173:
  ret i64 -1
dead174:
  ret i64 -1
dead175:
  ret i64 -1
dead176:
  ret i64 -1
dead177:
  ret i64 -1
dead178:
  ret i64 -1
dead179:
  ret i64 -1
dead180:
  ret i64 -1
dead181:
  ret i64 -1
dead182:
  ret i64 -1
dead183:
  ret i64 -1
dead184:
  ret i64 -1
dead185:
  ret i64 -1
dead186:
  ret i64 -1
dead187:
  ret i64 -1
dead188:
  ret i64 -1
dead189:
  ret i64 -1
dead190:
  ret i64 -1
dead191:
  ret i64 -1
dead192:
  ret i64 -1
dead193:
  ret i64 -1
dead194:
  ret i64 -1
dead195:
  ret i64 -1
dead196:
  ret i64 -1
dead197:
  ret i64 -1
dead198:
  ret i64 -1
dead199:
  ret i64 -1
dead200:
  ret i64 -1
dead201:
  ret i64 -1
dead202:
  ret i64 -1
dead203:
  ret i64 -1
dead204:
  ret i64 -1
dead205:
  ret i64 -1
dead206:
  ret i64 -1
dead207:
  ret i64 -1
dead208:
  ret i64 -1
dead209:
  ret i64 -1
dead210:
  ret i64 -1
dead211:
  ret i64 -1
dead212:
  ret i64 -1
dead213:
  ret i64 -1
dead214:
  ret i64 -1
dead215:
  ret i64 -1
dead216:
  ret i64 -1
dead217:
  ret i64 -1
dead218:
  ret i64 -1
dead219:
  ret i64 -1
dead220:
  ret i64 -1
dead221:
  ret i64 -1
dead222:
  ret i64 -1
dead223:
  ret i64 -1
dead224:
  ret i64 -1
dead225:
  ret i64 -1
dead226:
  ret i64 -1
dead227:
  ret i64 -1
dead228:
  ret i64 -1
dead229:
  ret i64 -1
dead230:
  ret i64 -1
dead231:
  ret i64 -1
dead232:
  ret i64 -1
dead233:
  ret i64 -1
dead234:
  ret i64 -1
dead235:
  ret i64 -1
dead236:
  ret i64 -1
dead237:
  ret i64 -1
dead238:
  ret i64 -1
dead239:
  ret i64 -1
dead240:
  ret i64 -1
dead241:
  ret i64 -1
dead242:
  ret i64 -1
dead243:
  ret i64 -1
dead244:
  ret i64 -1
dead245:
  ret i64 -1
dead246:
  ret i64 -1
dead247:
  ret i64 -1
dead248:
  ret i64 -1
dead249:
  ret i64 -1
dead250:
  ret i64 -1
dead251:
  ret i64 -1
dead252:
  ret i64 -1
dead253:
  ret i64 -1
dead254:
  ret i64 -1
dead255:
  ret i64 -1
dead256:
  ret i64 -1
dead257:
  ret i64 -1
dead258:
  ret i64 -1
dead259:
  ret i64 -1
dead260:
  ret i64 -1
dead261:
  ret i64 -1
dead262:
  ret i64 -1
dead263:
  ret i64 -1
dead264:
  ret i64 -1
dead265:
  ret i64 -1
dead266:
  ret i64 -1
dead267:
  ret i64 -1
dead268:
  ret i64 -1
dead269:
  ret i64 -1
dead270:
  ret i64 -1
dead271:
  ret i64 -1
dead272:
  ret i64 -1
dead273:
  ret i64 -1
dead274:
  ret i64 -1
dead275:
  ret i64 -1
dead276:
  ret i64 -1
dead277:
  ret i64 -1
dead278:
  ret i64 -1
dead279:
  ret i64 -1
dead280:
  ret i64 -1
dead281:
  ret i64 -1
dead282:
  ret i64 -1
dead283:
  ret i64 -1
dead284:
  ret i64 -1
dead285:
  ret i64 -1
dead286:
  ret i64 -1
dead287:
  ret i64 -1
dead288:
  ret i64 -1
dead289:
  ret i64 -1
dead290:
  ret i64 -1
dead291:
  ret i64 -1
dead292:
  ret i64 -1
dead293:
  ret i64 -1
dead294:
  ret i64 -1
dead295:
  ret i64 -1
dead296:
  ret i64 -1
dead297:
  ret i64 -1
dead298:
  ret i64 -1
dead299:
  ret i64 -1
dead300:
  ret i64 -1
dead301:
  ret i64 -1
dead302:
  ret i64 -1
dead303:
  ret i64 -1
dead304:
  ret i64 -1
dead305:
  ret i64 -1
dead306:
  ret i64 -1
dead307:
  ret i64 -1
dead308:
  ret i64 -1
dead309:
  ret i64 -1
dead310:
  ret i64 -1
dead311:
  ret i64 -1
dead312:
  ret i64 -1
dead313:
  ret i64 -1
dead314:
  ret i64 -1
dead315:
  ret i64 -1
dead316:
  ret i64 -1
dead317:
  ret i64 -1
dead318:
  ret i64 -1
dead319:
  ret i64 -1
dead320:
  ret i64 -1
dead321:
  ret i64 -1
dead322:
  ret i64 -1
dead323:
  ret i64 -1
dead324:
  ret i64 -1
dead325:
  ret i64 -1
dead326:
  ret i64 -1
dead327:
  ret i64 -1
dead328:
  ret i64 -1
dead329:
  ret i64 -1
dead330:
  ret i64 -1
dead331:
  ret i64 -1
dead332:
  ret i64 -1
dead333:
  ret i64 -1
dead334:
  ret i64 -1
dead335:
  ret i64 -1
dead336:
  ret i64 -1
dead337:
  ret i64 -1
dead338:
  ret i64 -1
dead339:
  ret i64 -1
dead340:
  ret i64 -1
dead341:
  ret i64 -1
dead342:
  ret i64 -1
dead343:
  ret i64 -1
dead344:
  ret i64 -1
dead345:
  ret i64 -1
dead346:
  ret i64 -1
dead347:
  ret i64 -1
dead348:
  ret i64 -1
dead349:
  ret i64 -1
dead350:
  ret i64 -1
dead351:
  ret i64 -1
dead352:
  ret i64 -1
dead353:
  ret i64 -1
dead354:
  ret i64 -1
dead355:
  ret i64 -1
dead356:
  ret i64 -1
dead357:
  ret i64 -1
dead358:
  ret i64 -1
dead359:
  ret i64 -1
dead360:
  ret i64 -1
dead361:
  ret i64 -1
dead362:
  ret i64 -1
dead363:
  ret i64 -1
dead364:
  ret i64 -1
dead365:
  ret i64 -1
dead366:
  ret i64 -1
dead367:
  ret i64 -1
dead368:
  ret i64 -1
dead369:
  ret i64 -1
dead370:
  ret i64 -1
dead371:
  ret i64 -1
dead372:
  ret i64 -1
dead373:
  ret i64 -1
dead374:
  ret i64 -1
dead375:
  ret i64 -1
dead376:
  ret i64 -1
dead377:
  ret i64 -1
dead378:
  ret i64 -1
dead379:
  ret i64 -1
dead380:
  ret i64 -1
dead381:
  ret i64 -1
dead382:
  ret i64 -1
dead383:
  ret i64 -1
dead384:
  ret i64 -1
dead385:
  ret i64 -1
dead386:
  ret i64 -1
dead387:
  ret i64 -1
dead388:
  ret i64 -1
dead389:
  ret i64 -1
dead390:
  ret i64 -1
dead391:
  ret i64 -1
dead392:
  ret i64 -1
dead393:
  ret i64 -1
dead394:
  ret i64 -1
dead395:
  ret i64 -1
dead396:
  ret i64 -1
dead397:
  ret i64 -1
dead398:
  ret i64 -1
dead399:
  ret i64 -1
}

define i64 @loop(i64 %n) {
entry:
  br label %header
header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %cond = icmp slt i64 %i, %n
  br i1 %cond, label %body, label %exit
body:
  %i.next = call i64 @f(i64 %i)
  br label %header
exit:
  ret i64 %i
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @loop(i64 40000)
  ret i64 %r
}

; ASSERT EQ: i64 40000 = call i64 @main(i64 0, i8** null)
