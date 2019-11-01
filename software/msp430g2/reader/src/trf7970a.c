//==============================================================================
/*! \file     trf7970a.c
    \brief    Code for configuring and talking to the TRF7970A
    \author   Andrew Parlane
*/
//==============================================================================

#include "trf7970a.h"
#include "time.h"
#include "spi.h"
#include "uart.h"
#include "gpio.h"

#include <msp430.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

// This is just for testing the prescence of the TRF7970A ATM
static uint8_t read_ram_byte(void)
{
    return trf7970a_read_register(TRF7970A_REG_RAM_1);
}

// This is just for testing the prescence of the TRF7970A ATM
static void write_ram_byte(uint8_t val)
{
    trf7970a_write_register(TRF7970A_REG_RAM_1, val);
}

bool trf7970a_init(void)
{
    // initialise our outputs
    GPIO_DEASSERT_TRF7970A_SS();
    GPIO_DEASSERT_TRF7970A_EN();

    // leave the TRF7970A in reset for 100ms
    // then power it up and wait another 100ms
    // I can't find much information on timing for resets, but this should be plenty
    sleep_ms(100);
    GPIO_ASSERT_TRF7970A_EN();
    sleep_ms(100);

    // There doesn't appear to be an ID register to confirm that the TRF7970A is present
    // so read from the RAM reg, write it back + 0x42, and read it back again
    uint8_t ram = read_ram_byte();
    uint8_t ram2 = ram+0x42;
    write_ram_byte(ram2);
    uint8_t ram3 = read_ram_byte();

    /* uart_puts("initial: ");
    uart_put_hex_byte(ram);
    uart_puts(", wrote: ");
    uart_put_hex_byte(ram2);
    uart_puts(", read: ");
    uart_put_hex_byte(ram3);
    uart_puts("\n"); */

    if (ram3 != (ram2))
    {
        return false;
    }

    // Initialisation sequence taken from the TRF7970A datasheet section 6.11

    // 1) Raise EN - already done

    // 2) Issue a Software Initialization direct command (0x03),
    //    followed by an Idle direct command (0x00) to soft reset the TRF7970A.
    trf7970a_send_direct_command(TRF7970A_CMD_SW_INIT);
    trf7970a_send_direct_command(TRF7970A_CMD_IDLE);

    // 3) Delay 1 ms to allow the TRF7970A to fully process the soft reset.
    // ATM our sleep_ms command is not accurate. It has 2ms resolution,
    // and the IRQ could have just occurred or be just about to occur.
    // to guarantee at least 1ms occurs, we have to timeout after 4ms
    sleep_ms(4);

    // 4) Issue a Reset FIFO direct command (0x0F).
    trf7970a_send_direct_command(TRF7970A_CMD_RESET_FIFO);

    // 5) Write the Modulator and SYS_CLK Control register (0x09) with the appropriate
    //    application-specific setting for the crystal and system clock settings.
    // 13.56MHz OSC                         - 0x00
    // Modulation as defined by B0 to B2    - 0x00
    // SYS_CLK output disabled              - 0x00
    // ASK/OOK normal                       - 0x00
    // ASK 100%                             - 0x01
    trf7970a_write_register(TRF7970A_REG_MODULATOR_SYS_CLK_CONTROL, 0x01);

    // 6) (Optional) Write the Regulator and I/O Control register (0x0B) with the
    //    appropriate application-specific setting.
    // Not exactly sure what this is for, it appears mostly unused. Using 0x01
    // Which comes from the DLP-7970ABP demo project.
    trf7970a_write_register(TRF7970A_REG_REGULATOR_IO_CONTROL, 0x01);

    // 7) Write the NFC Target Detection Level register (0x18) with the value of 0x00.
    //    For details on this requirement, see the TRF7970A Silicon Errata.
    trf7970a_write_register(TRF7970A_REG_NFC_TARGET_DETECTION_LEVEL, 0x00);

    return true;
}

void trf7970a_send_direct_command(uint8_t cmd)
{
    cmd = TRF7970A_ADDR_CMD_BYTE_CMD(cmd);
    spi_tfer(&cmd, 1, NULL, 0);
}

void trf7970a_write_register(uint8_t addr, uint8_t val)
{
    uint8_t txBuf[2] = {TRF7970A_ADDR_CMD_BYTE_WRITE_ADDR(addr), val};
    spi_tfer(txBuf, 2, NULL, 0);
}

void trf7970a_write_registers_cont(uint8_t addr, const uint8_t *buf, uint16_t len)
{
    uint8_t addrByte = TRF7970A_ADDR_CMD_BYTE_WRITE_ADDR_CONT(addr);
    spi_tfer_ext(&addrByte, 1, buf, len, NULL, 0);
}

uint8_t trf7970a_read_register(uint8_t addr)
{
    addr = TRF7970A_ADDR_CMD_BYTE_READ_ADDR(addr);
    uint8_t rxVal;

    spi_tfer(&addr, 1, &rxVal, 1);
    return rxVal;
}

void trf7970a_read_register_cont(uint8_t addr, uint8_t *buf, uint16_t len)
{
    addr = TRF7970A_ADDR_CMD_BYTE_READ_ADDR_CONT(addr);

    spi_tfer(&addr, 1, buf, len);
}

// data is a buffer of length len bytes.
// if brokenBits == 0, we transmit len bytes
// else, we transmit (len-1) bytes + brokenBits bits (max 7 bits)
void trf7970a_tx_without_crc(const uint8_t *data, uint16_t len, uint8_t brokenBits)
{
    // The FIFO is 127 bytes long, I don't support sending more than that yet.
    if ((len == 0) || (len > 127))
    {
        return;
    }

    if (brokenBits > 7)
    {
        return;
    }

    // Calculate the byte and bit lengths
    // The length field is two bytes (see Table 6-57 and 6-58 in the TRF7970A datasheet)
    //   1) 7:0 - num bytes to Tx, bits 11:4
    //   2) 7:4 - num bytes to Tx, bits 3:0
    //      3:1 - num broken bits to send
    //        0 - send broken bits (0 -> whole number of bytes)
    uint16_t bytes;
    if (brokenBits == 0)
    {
        bytes = len;
    }
    else
    {
        bytes = len-1;
        brokenBits = (brokenBits << 1) | 0x01;
    }

    // For this to work the TRF7970A_CMD_TX_WITHOUT_CRC, two length registers and the fifo data
    // must be in the same transaction. The TRF7970A_CMD_RESET_FIFO can be separate but we may
    // as well add it in.

    uint8_t txBuf[5] =
    {
        // First reset the FIFO
        TRF7970A_ADDR_CMD_BYTE_CMD(TRF7970A_CMD_RESET_FIFO),
        // then send the Tx without CRC command
        TRF7970A_ADDR_CMD_BYTE_CMD(TRF7970A_CMD_TX_WITHOUT_CRC),
        // Write continuous, starting with the TX len 1 register
        TRF7970A_ADDR_CMD_BYTE_WRITE_ADDR_CONT(TRF7970A_REG_TX_LEN_1),
        // Tx len 1
        (bytes >> 4) & 0xFF,
        // Tx len 2
        ((bytes & 0x0F) << 4) | brokenBits,
    };

    spi_tfer_ext(txBuf, 5, data, len, NULL, 0);
}

bool trf7970a_detect_other_rf_fields(void)
{
    // This proceedure is taken from the TRF7970A errata, section:
    //      "RF Collision Avoidance Direct Commands do not behave as expected"

    // 1. Write a 0x02 (3-VDC operation) or 0x03 (5-VDC operation) to the Chip Status Control
    //    register (0x00) to disable the transmitter and enable the receiver.
    trf7970a_write_register(TRF7970A_REG_STATUS_CONTROL, 0x02);

    // 2. Send a Test External RF direct command (0x19).
    trf7970a_send_direct_command(TRF7970A_CMD_TEST_EXTERNAL_RF);

    // 3. Delay 50 µs to allow the transceiver to measure the field strength and latch the value
    //    into the RSSI register.
    sleep_ms(4);    // 4ms guarantees at least 2ms of delay

    // 4. Read the RSSI Levels and Oscillator Status register (0x0F).
    uint8_t res = trf7970a_read_register(TRF7970A_REG_RSSI_LEVEL_OSC_STATUS);

    // 5. If the active channel RSSI value (bits 2:0) is greater than 0, remain in target mode for
    //     a predetermined time (number of milliseconds).
    // 6. If the active channel RSSI value (bits 2:0) is equal to 0, enter initiator or target mode
    //    for active or passive communication.

    // disable the receiver
    trf7970a_write_register(TRF7970A_REG_STATUS_CONTROL, 0x00);

    if ((res & 0x03) != 0)
    {
        // RF field detected
        return true;
    }
    else
    {
        // No RF field detected
        return false;
    }
}
