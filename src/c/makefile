#------------------------------------------------------------------
# makefile
#
# Copyright (c) 2009 by cisco Systems, Inc. 
# All rights reserved. 
#------------------------------------------------------------------

RM = rm
CC = gcc

CFLAGS = -g 
LDFLAGS = -lm

#OBJ = cparse.o codespace.o

WRSORT = wrsort.exe
ALLTARGET = $(WRSORT)

%.exe : %.o
	$(CC) $? $(LDFLAGS) -o $@

%.o : %.c
	$(CC) -c $(CFLAGS) $? -o $@

%.o : %.cpp
#	$(CC) -c $(CFLAGS) $? -o $@

all : $(ALLTARGET)

#$(TARGET) : $(OBJ)
#	$(CC) $^ $(LDFLAGS) -o $@

clean:
	$(RM) *.o *.exe

