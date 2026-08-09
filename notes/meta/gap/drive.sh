#!/bin/bash
cd "$(dirname "$0")"
: > cases.log
for d in "12 3" "21 1" "39 1" "48 3" "57 1"; do
  set -- $d; D1=$1; D2=$2
  for pi in 1 2 3 4 5 6; do
    stop=0
    for ue in 1 3 9; do
      sed -e "s/DID1/$D1/g" -e "s/DID2/$D2/g" -e "s/PAIRIDX/$pi/g" -e "s/UEXP/$ue/g" one.g > _c_${D1}_${pi}_${ue}.g
      out=$(timeout 300 ~/gap-4.16.0/gap -q -b _c_${D1}_${pi}_${ue}.g 2>&1 | grep -E "^D=\[|^NOPAIR|CANDIDATE")
      if echo "$out" | grep -q NOPAIR; then stop=1; break; fi
      if [ -z "$out" ]; then out="D=[$D1,$D2] pair=$pi uexp=$ue  TIMEOUT-or-ERROR (enumeration too hard; Gamma may be infinite)"; fi
      echo "$out" >> cases.log
    done
    [ $stop -eq 1 ] && break
  done
done
echo "ALLDONE" >> cases.log
