/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "common.h"

int main(int argc,char **argv){
 setvbuf(stdout,NULL,_IOLBF,0);
 if(argc<4)fail("usage: probe describe ELF SECTION | capture ELF SECTION METADATA OUTPUT | native-controls ELF SECTION METADATA | verify/dump ELF SECTION METADATA CAPTURES SHA256 | parser-controls ELF SECTION METADATA CAPTURES");
 if(!strcmp(argv[1],"describe") && argc==4){authenticate(argv[2],argv[3],NULL);metadata(stdout);return 0;}
 if(argc<5)fail("metadata required");
 authenticate(argv[2],argv[3],argv[4]);
 if(!strcmp(argv[1],"capture") && argc==6){capture_all(argv[5]);return 0;}
 if(!strcmp(argv[1],"native-controls") && argc==5){native_controls();return 0;}
 if(!strcmp(argv[1],"verify") && argc==7){verify_file(argv[5],argv[6]);return 0;}
 if(!strcmp(argv[1],"dump") && argc==7){verify_file(argv[5],argv[6]);dump_file(argv[5]);return 0;}
 if(!strcmp(argv[1],"parser-controls") && argc==6){parser_controls(argv[5]);return 0;}
 if(!strcmp(argv[1],"auth-controls") && argc==7){auth_controls(argv[2],argv[3],argv[4],argv[5],argv[6]);return 0;}
 fail("invalid command or argument count");return 2;
}
