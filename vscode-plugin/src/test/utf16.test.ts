import * as assert from "assert"
import {UTF16CodeUnitOffsetToCharOffset, charOffsetToUTF16CodeUnitOffset} from "../extension"

suite("UTF-16 offset conversion", () => {
    test("an offset inside a surrogate pair is rejected", () => {
        assert.throws(() => UTF16CodeUnitOffsetToCharOffset(1, "😀"))
    })

    test("conversions round-trip on random strings with astral characters", () => {
        const alphabet = ["a", "😀", "\n", "é", "𝄞", "\r"]
        let seed = 12345
        const random = (n: number) => {
            seed = (seed * 1103515245 + 12345) % 2147483648
            return seed % n
        }
        for (let i = 0; i < 500; i++) {
            let content = ""
            for (let len = random(12); len > 0; len--) {
                content += alphabet[random(alphabet.length)]
            }
            const chars = [...content].length
            for (let c = 0; c <= chars; c++) {
                const u = charOffsetToUTF16CodeUnitOffset(c, content)
                assert.ok(u >= 0 && u <= content.length)
                assert.strictEqual(UTF16CodeUnitOffsetToCharOffset(u, content), c)
            }
            for (let u = 0; u <= content.length; u++) {
                const interior =
                    u > 0 &&
                    u < content.length &&
                    content.charCodeAt(u - 1) >= 0xd800 &&
                    content.charCodeAt(u - 1) <= 0xdbff
                if (interior) {
                    assert.throws(() => UTF16CodeUnitOffsetToCharOffset(u, content), content)
                } else {
                    const c = UTF16CodeUnitOffsetToCharOffset(u, content)
                    assert.ok(c >= 0 && c <= chars)
                    assert.strictEqual(charOffsetToUTF16CodeUnitOffset(c, content), u)
                }
            }
        }
    })
})
