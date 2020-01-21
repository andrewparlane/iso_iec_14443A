The emulation project allows me to run the ISO1443 system and sensor control system in an FPGA.
The TRF7970A is used as an analogue front end (AFE), allowing us to test the digital part before
fabricating the ASIC.

I am using a Terasic DE2 Dev board: https://www.terasic.com.tw/cgi-bin/page/archive.pl?No=30
    contains an Altera (Intel) Cyclone II 2C35 FPGA.
    Has 50MHz and 27MHz clock inputs

Clock
    I haven't found a way to get the recovered clock from the carrier wave out of the TRF7970A.
    There is the SYS_CLOCK output, but I think that comes from the crystal on the dev board
    and not from the carrier wave. Additionally that signal only goes to a testpoint, which is
    hidden behind the module's shield.
    Instead I use the 50MHz clock input to the FPGA with a PLL to generate a 13.54MHz clock.
    This is not within spec, but I think the TRF7970A should be a bit more forgiving.
    Additionally this project is just to give us a better idea of if the design will work in an ASIC
    and doesn't have to be a perfect mock up.

Logic:
    Since in the real design the clock stops during pauses, I emulate that here too.
    The 13.56MHz clock goes through a clock control block, allowing me to enable or disable it
    at will.
    The pause signal is synchronised to the 50MHz clock. Upon detecting the falling edge,
    we disable the 13.56MHz clock. Upon detecting the rising edge, we re-enable it.
    The unsynchronised pause signal is also passed directly to the ISO1443 system, where it is
    passes through a reset synchroniser.

Physical setup:
    Take the EXP-MSP430G2 eval board and connect it to the DLP-7970A booseter pack.
    Program it with the software/msp430/card_emulation_dm0 project.
    Connect the MISO pin J2.14 (p1.6) of the eval boardsr to JP1.1 (GPIO_0[0] / IO_A0)
        of the DE2 FPGA eval board.
    Take another EXP-MSP430G2 eval board + DLP-7970A booster pack and program them with the
        software/msp430/reader project.
    Power everything up
    reset the FPGA design with KEY[0]
    Put the two booster pack boards' antennas in proximity to each other.

Notes:
    Currently Tx is not supported. This should come soon.
    Currently the only way to check if it's working, is to use signaltap.
        Once I've added Tx, we should be able to set up a ping test
        and later actual initialisation and anticollision