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

		<% for (var i = 0; i < method.tests.length; i++) { %>
		[TestMethod]
		public void <%= method.tests[i].name %>()
		{
			testee.<%= method.name %>(<%= method[i].argumentString %>);
		}
		<% } %>
	}
}
