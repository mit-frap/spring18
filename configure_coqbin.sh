coq_path=$(echo `which coqc`)
coq_dir_path=${coq_path%/*}
coq_dir_path_slash="$coq_dir_path/"

export COQBIN=$coq_dir_path_slash
echo "Successfully exported COQBIN: $COQBIN"
