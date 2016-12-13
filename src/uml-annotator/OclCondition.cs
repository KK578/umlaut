using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		public OclComparison Comparator { get; set; }
		private List<string> arguments;
		private string exception;

		public OclCondition()
		{
			arguments = new List<string>();
		}

		public OclCondition(string condition)
		{
			string innerCondition = condition;
			if (innerCondition.StartsWith("("))
			{
				innerCondition = innerCondition.Substring(1, innerCondition.Length - 2);
			}

			string[] items = innerCondition.Split(' ');
			Comparator = FindComparison(items[0]);

			arguments = new List<string>();
			for (int i = 1; i < items.Length; i++)
			{
				arguments.Add(items[i]);
			}
		}

		public void SetArguments(string argument)
		{
			arguments = new List<string>(Regex.Split(argument, "\r?\n"));
		}

		public string GetArgumentsString()
		{
			return String.Join("\r\n", arguments);
		}

		public void SetException(string ex)
		{
			if (!String.IsNullOrWhiteSpace(ex))
			{
				exception = String.Format("(Exception:{0})", ex);
			}
			else
			{
				exception = "";
			}
		}

		private OclComparison FindComparison(string comparison)
		{
			// HACK: See MainWindow for explanation.
			List<OclComparison> comparisons = MainWindow.comparisonList;

			foreach (OclComparison c in comparisons)
			{
				if (comparison == c.SymbolString())
				{
					return c;
				}
			}

			return null;
		}

		public override string ToString()
		{
			string comparison = "";

			if (Comparator != null)
			{
				comparison = Comparator.SymbolString();
			}

			string main = String.Format("{0} {1}", comparison, String.Join(" ", arguments));
			string result;

			if (!String.IsNullOrWhiteSpace(exception))
			{
				result = String.Format("({0} {1})", main, exception);
			}
			else
			{
				result = String.Format("({0})", main);
			}

			return result;
		}
	}
}
