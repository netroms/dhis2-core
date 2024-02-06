/*
 * Copyright (c) 2004-2022, University of Oslo
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 * Neither the name of the HISP project nor the names of its contributors may
 * be used to endorse or promote products derived from this software without
 * specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.hisp.dhis.analytics.table.model;

import static org.hisp.dhis.db.model.Table.fromStaging;
import static org.hisp.dhis.db.model.Table.toStaging;

import java.util.Date;
import java.util.List;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import org.hisp.dhis.analytics.AnalyticsTableType;
import org.hisp.dhis.commons.collection.UniqueArrayList;
import org.hisp.dhis.db.model.Column;
import org.hisp.dhis.db.model.Logged;
import org.hisp.dhis.program.Program;
import org.hisp.dhis.trackedentity.TrackedEntityType;
import org.springframework.util.Assert;

/**
 * Class representing an analytics database table. Note that the table name initially represents a
 * staging table. The name of the main table can be retrieved with {@link
 * AnalyticsTable#getMainName()}.
 *
 * @author Lars Helge Overland
 */
@Getter
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class AnalyticsTable {
  /** Table name. */
  @EqualsAndHashCode.Include private final String name;

  /** Analytics table type. */
  private final AnalyticsTableType tableType;

  /** Columns representing dimensions. */
  private final List<AnalyticsTableColumn> analyticsTableColumns;

  /** Whether table is logged or unlogged. PostgreSQL-only feature. */
  private final Logged logged;

  /** Program of events in analytics table. */
  private Program program;

  /** Tracked entity type of enrollments in analytics table. */
  private TrackedEntityType trackedEntityType;

  /** Analytics table partitions for this base analytics table. */
  private List<AnalyticsTablePartition> tablePartitions = new UniqueArrayList<>();

  // -------------------------------------------------------------------------
  // Constructors
  // -------------------------------------------------------------------------

  /**
   * Constructor. Sets the name to represent a staging table.
   *
   * @param tableType the {@link AnalyticsTableType}.
   * @param columns the list of {@link Column}.
   * @param logged the {@link Logged} property.
   */
  public AnalyticsTable(
      AnalyticsTableType tableType, List<AnalyticsTableColumn> columns, Logged logged) {
    this.name = toStaging(tableType.getTableName());
    this.tableType = tableType;
    this.analyticsTableColumns = columns;
    this.logged = logged;
  }

  /**
   * Constructor. Sets the name to represent a staging table.
   *
   * @param tableType the {@link AnalyticsTableType}.
   * @param columns the list of {@link Column}.
   * @param logged the {@link Logged} property.
   * @param program the {@link Program}.
   */
  public AnalyticsTable(
      AnalyticsTableType tableType,
      List<AnalyticsTableColumn> columns,
      Logged logged,
      Program program) {
    this.name = toStaging(getTableName(tableType, program));
    this.tableType = tableType;
    this.analyticsTableColumns = columns;
    this.logged = logged;
    this.program = program;
  }

  /**
   * Constructor. Sets the name to represent a staging table.
   *
   * @param tableType the {@link AnalyticsTableType}.
   * @param columns the list of {@link Column}.
   * @param logged the {@link Logged} property.
   * @param trackedEntityType the {@link TrackedEntityType}.
   */
  public AnalyticsTable(
      AnalyticsTableType tableType,
      List<AnalyticsTableColumn> columns,
      Logged logged,
      TrackedEntityType trackedEntityType) {
    this.name = toStaging(getTableName(tableType, trackedEntityType));
    this.tableType = tableType;
    this.analyticsTableColumns = columns;
    this.logged = logged;
    this.trackedEntityType = trackedEntityType;
  }

  // -------------------------------------------------------------------------
  // Static methods
  // -------------------------------------------------------------------------

  /**
   * Converts the given list of analytics table columns to a list of columns.
   *
   * @param columns the list of {@link AnalyticsTableColumn}.
   * @return a list of {@link Column}.
   */
  protected static List<Column> toColumns(List<AnalyticsTableColumn> columns) {
    return columns.stream()
        .map(c -> new Column(c.getName(), c.getDataType(), c.getNullable(), c.getCollation()))
        .toList();
  }

  /**
   * Returns a table name.
   *
   * @param tableType the {@link AnalyticsTableType}.
   * @param program the {@link Program}.
   * @return the table name.
   */
  public static String getTableName(AnalyticsTableType tableType, Program program) {
    return tableType.getTableName() + "_" + program.getUid().toLowerCase();
  }

  /**
   * Returns a table name.
   *
   * @param tableType the {@link AnalyticsTableType}.
   * @param trackedEntityType the {@link TrackedEntityType}.
   * @return the table name.
   */
  public static String getTableName(
      AnalyticsTableType tableType, TrackedEntityType trackedEntityType) {
    return tableType.getTableName() + "_" + trackedEntityType.getUid().toLowerCase();
  }

  // -------------------------------------------------------------------------
  // Logic methods
  // -------------------------------------------------------------------------

  /**
   * Returns the name which represents the main analytics table.
   *
   * @return the name which represents the main analytics table.
   */
  public String getMainName() {
    return fromStaging(name);
  }

  /**
   * Returns columns of analytics value type dimension.
   *
   * @return a list of {@link AnalyticsTableColumn}.
   */
  public List<AnalyticsTableColumn> getDimensionColumns() {
    return analyticsTableColumns.stream()
        .filter(c -> AnalyticsValueType.DIMENSION == c.getValueType())
        .toList();
  }

  /**
   * Returns columns of analytics value type fact.
   *
   * @return a list of {@link AnalyticsTableColumn}.
   */
  public List<AnalyticsTableColumn> getFactColumns() {
    return analyticsTableColumns.stream()
        .filter(c -> AnalyticsValueType.FACT == c.getValueType())
        .toList();
  }

  /**
   * Returns the count of all columns.
   *
   * @return the count of all columns.
   */
  public int getColumnCount() {
    return getAnalyticsTableColumns().size();
  }

  /**
   * Indicates whether the table is unlogged.
   *
   * @return true if the table is unlogged.
   */
  public boolean isUnlogged() {
    return Logged.UNLOGGED == logged;
  }

  /**
   * Adds an analytics partition table to this master table.
   *
   * @param checks the partition checks.
   * @param year the year.
   * @param startDate the start date.
   * @param endDate the end date.
   * @return this analytics table.
   */
  public AnalyticsTable addTablePartition(
      List<String> checks, Integer year, Date startDate, Date endDate) {
    Assert.notNull(year, "Year must be specified");

    AnalyticsTablePartition tablePartition =
        new AnalyticsTablePartition(this, checks, year, startDate, endDate);

    this.tablePartitions.add(tablePartition);

    return this;
  }

  /**
   * Indicates whether this analytics table has any partitions.
   *
   * @return true if this analytics table has any partitions.
   */
  public boolean hasTablePartitions() {
    return !tablePartitions.isEmpty();
  }

  /**
   * Returns the latest partition, or null if no latest partition exists.
   *
   * @return a {@link AnalyticsTablePartition} or null.
   */
  public AnalyticsTablePartition getLatestTablePartition() {
    return tablePartitions.stream()
        .filter(AnalyticsTablePartition::isLatestPartition)
        .findAny()
        .orElse(null);
  }

  @Override
  public String toString() {
    return "[Table name: " + getName() + ", partitions: " + tablePartitions + "]";
  }
}