import unittest

from string_interner import StringInterner

class StringInternerTestCase(unittest.TestCase):
    def setUp(self):
        self.s = StringInterner()

    def test_has_string_with_add(self):
        self.assertFalse(self.s.has_string("asdf"))
        self.s.add("asdf")
        self.assertTrue(self.s.has_string("asdf"))

    def test_has_string_with_get_int_or_add(self):
        self.assertFalse(self.s.has_string("asdf"))
        self.s.get_int_or_add("asdf")
        self.assertTrue(self.s.has_string("asdf"))

    def test_get_int_or_add_uniqueness(self):
        x = self.s.get_int_or_add("x")
        y = self.s.get_int_or_add("y")
        z = self.s.get_int_or_add("z")

        self.assertNotEquals(x, y)
        self.assertNotEquals(x, z)
        self.assertNotEquals(y, z)

    def test_get_int_or_add_consistency(self):
        x1 = self.s.get_int_or_add("x")
        y = self.s.get_int_or_add("y")
        x2 = self.s.get_int_or_add("x")
        z = self.s.get_int_or_add("z")
        x3 = self.s.get_int_or_add("x")

        self.assertEquals(x1, x2)
        self.assertEquals(x1, x3)

    def test_get_str(self):
        x = self.s.get_int_or_add("x")
        y = self.s.get_int_or_add("y")
        z = self.s.get_int_or_add("z")

        self.assertEquals(self.s.get_str(x), "x")
        self.assertEquals(self.s.get_str(y), "y")
        self.assertEquals(self.s.get_str(z), "z")

    def test_get_int(self):
        x = self.s.get_int_or_add("x")
        y = self.s.get_int_or_add("y")
        z = self.s.get_int_or_add("z")

        self.assertEquals(self.s.get_int("x"), x)
        self.assertEquals(self.s.get_int("y"), y)
        self.assertEquals(self.s.get_int("z"), z)
