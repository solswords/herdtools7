#!/bin/bash


aslfile="$1"
base=`basename "$aslfile"`
astfile="$base".lsp
outfile="$base".out

scriptdir="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
acl2asldir=$(cd "$scriptdir"/../; pwd)

export ACL2_PROJECTS="$acl2asldir"/PROJECT_DIRS
export PATH="$acl2asldir"/bin:$PATH

if ! ( aslref --print-lisp --no-exec "$aslfile" > "$astfile" ); then
    echo "aslref error"
    exit 1;
fi

echo "(asl::read-ast-file-into-globals \"$astfile\") (ld \"${acl2asldir}/run-test.lsp\")" | acl2asl > "$outfile"

status=$?

start_pattern='!@#$%^%$#@ begin ASL interpreter output'
end_pattern='!@#$%^%$#@ end ASL interpreter output'

if ! ( fgrep -q "$start_pattern" "$outfile" > /dev/null &&
	   fgrep -q "$end_pattern" "$outfile" > /dev/null ) then
   echo "ACL2 failed to run ASL interpretation"
   exit 1;
fi

# generated by chatgpt
awk -v start="$start_pattern" -v end="$end_pattern" '
    index($0, start) {flag=1; next} 
    index($0, end) && flag {exit} 
    flag { printf "%s", sep $0; sep=ORS }' "$outfile"

exit $status
