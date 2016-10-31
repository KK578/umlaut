using System;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace AutomatedTestSuite
{
	[TestClass]
	public class UnitTestClass
	{
		SimpleMath testee;

        [TestInitialize]
        public void Initialize()
        {
            testee = new SimpleMath();
        }

		<% for (var i = 0; i < methods.length; i++) { %>
		<% for (var j = 0; j < methods[i].tests.length; j++) { %>
		<% if (methods[i].tests[j]) { %>
		[TestMethod]
		public void <%= methods[i].tests[j].name %>()
		{
			testee.<%= methods[i].name %>(<%= methods[i].tests[j].argumentString %>);
		}
		<% } %>
		<% } %>
		<% } %>
	}
}
