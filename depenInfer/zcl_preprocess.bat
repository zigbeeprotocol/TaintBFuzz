"C:\Program Files (x86)\IAR Systems\Embedded Workbench 8.3\arm\bin\iccarm.exe" zcl.c -I F:\Workspace\frama-c\frama-c-master\src -I F:\Workspace\frama-c\frama-c-master\share\libc -I . --preprocess=cn "zcl.i" -D __FC_MACHDEP_X86_32 --silent -f "F:\Workspace\zigbfuzz\depenInfer\compile_config.xcl"

copy /y zcl.i zcl_annot.i