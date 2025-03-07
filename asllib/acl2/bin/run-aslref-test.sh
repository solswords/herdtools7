#!/bin/bash



# Initialize variables
incompatible=0
notypecheck=0
aslargs=()
aslfile=""

# Process arguments
for arg in "$@"; do
    if [[ "$arg" == "--no-exec" || "$arg" == "--no-type-check" || "$arg" == "-0" ]]; then
        incompatible=1
	aslargs+=("$arg")
    else
        aslargs+=("$arg")
    fi
done

# If incompatible, just run aslref to get the expected output
if [[ $incompatible == 1 ]]; then
    exec aslref ${aslargs[@]} ;
fi

# Extract the last argument as aslfile
if [[ ${#aslargs[@]} -gt 0 ]]; then
    aslfile=${aslargs[${#aslargs[@]}-1]}
    unset aslargs[${#aslargs[@]}-1]  # Remove last element from aslargs
else
    echo "not enough arguments"
    exit 1;
fi

# echo "incompatible=$incompatible"
# echo "aslargs=${aslargs[@]}"
# echo "aslfile=$aslfile"

base=`basename "$aslfile"`
astfile="$base".lsp
outfile="$base".out

scriptdir="$( cd -- $(dirname $0) >/dev/null 2>&1 ; pwd -P )"
acl2asldir=$(cd "$scriptdir"/../; pwd)

export ACL2_PROJECTS="$acl2asldir"/PROJECT_DIRS
export PATH="$acl2asldir"/bin:$PATH

# echo aslref ${aslargs[@]} "$aslfile" --no-exec;
# echo aslref ${aslargs[@]} "$aslfile --print-lisp --no-exec";

# echo aslref ${aslargs[@]} "$aslfile" --print-lisp --no-exec
aslref_out=$( ( aslref ${aslargs[@]} "$aslfile" --print-lisp --no-exec > "$astfile" ) 2>&1 )
if [[ $? != 0 ]]; then
    # echo "aslref_out (fail before exec):"
    echo "$aslref_out";
    exit 1;
fi

echo "(asl::read-ast-file-into-globals \"$astfile\")
    (acl2::update-oracle-mode 1 asl::orac) ;; HACK -- Set the oracle to deterministic mode for compatibility
    (ld \"${acl2asldir}/run-test.lsp\")" | acl2asl > "$outfile"

status=$?

start_pattern='!@#$%^%$#@ begin ASL interpreter output'
end_pattern='!@#$%^%$#@ end ASL interpreter output'

if ! ( fgrep -q "$start_pattern" "$outfile" > /dev/null &&
	   fgrep -q "$end_pattern" "$outfile" > /dev/null ); then
    echo "ACL2 failed to run ASL interpretation"
    exit 1;
fi

# echo aslref ${aslargs[@]} "$aslfile"
# Hack: rerun aslref for the error message and quit without printing our output
if [[ $status != 0 ]]; then
    aslref ${aslargs[@]} "$aslfile"
    refstatus=$?
    if [[ $refstatus == 0 ]]; then
	echo "aslref status mismatched"
    fi
    exit $refstatus
fi

# echo "aslref_out (success):"
if [[ "$aslref_out" != "" ]]; then
    echo "$aslref_out";
fi
   
# generated by chatgpt
awk -v start="$start_pattern" -v end="$end_pattern" '
    index($0, start) {flag=1; next} 
    index($0, end) && flag {exit} 
    flag { printf "%s", sep $0; sep=ORS }' "$outfile"


exit $status
