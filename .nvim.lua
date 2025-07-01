require("razzle")
require("razzle.zen-mode")

motion = require("razzle.motion")
vim.keymap.set("n", "]S", motion.next_slide)
vim.keymap.set("n", "[S", motion.prev_slide)
